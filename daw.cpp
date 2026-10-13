// ============================================================================
// daw.cpp - Workshop DAW for Win32. Uses only windows.h, winmm and gdi32.
//
// Build (MinGW-w64):
//   g++ -std=c++17 -O2 -Wall -Wextra -Wconversion daw.cpp -o daw.exe -lwinmm -lgdi32 -mwindows
// Build (MSVC, Developer Prompt):
//   cl /std:c++17 /O2 /W4 /EHsc daw.cpp
//
// Contents:
//   - Transport (Play/Stop, BPM) driving a 32-step piano roll
//   - Polyphonic saw synth (8 voices) playing the roll and the on-screen piano
//   - Live microphone channel (waveIn) with real-time pitch correction
//   - Master meter and pitch readout
//
// Threading:
//   UI thread      : window messages, drawing from a snapshot
//   audio thread   : pulls blocks and writes them to waveOut (CALLBACK_EVENT)
//   mic callback   : waveIn driver thread, pushes into a lock-free ring
// ============================================================================

#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <mmsystem.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#if defined(_MSC_VER)
#pragma comment(lib, "winmm.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")
#endif

namespace {

// ---------------------------------------------------------------- Design tokens
// Baseline dark theme (AGENTS.md 6.9). All colors, sizes and spacing live here;
// drawing code refers to these names only.
namespace tok {
constexpr COLORREF kCanvas = RGB(14, 16, 22);        // neutral-950
constexpr COLORREF kSurface = RGB(23, 26, 34);       // neutral-900
constexpr COLORREF kRaised = RGB(38, 43, 54);        // neutral-800
constexpr COLORREF kHover = RGB(58, 65, 80);         // neutral-700
constexpr COLORREF kBorder = RGB(58, 65, 80);        // neutral-700
constexpr COLORREF kText = RGB(247, 248, 250);       // neutral-50
constexpr COLORREF kTextDim = RGB(196, 202, 213);    // neutral-300
constexpr COLORREF kTextDisabled = RGB(107, 116, 136);  // neutral-500
constexpr COLORREF kAccent = RGB(142, 162, 255);     // dark-mode accent
constexpr COLORREF kAccentPressed = RGB(38, 59, 148);
constexpr COLORREF kDanger = RGB(255, 140, 128);
constexpr COLORREF kKeyWhite = RGB(232, 235, 242);
constexpr COLORREF kKeyBlack = RGB(40, 44, 56);

constexpr int kRadius = 6;
constexpr int kSpace8 = 8;
constexpr int kTopH = 52;
constexpr int kRulerH = 24;
constexpr int kTrackW = 170;
constexpr int kKeysW = 56;
constexpr int kCellW = 24;
constexpr int kCellH = 16;
constexpr int kStatusH = 32;
}  // namespace tok

// ---------------------------------------------------------------- Constants
constexpr int kSr = 44100;
constexpr int kBlock = 512;       // frames per output buffer
constexpr int kOutBuffers = 3;
constexpr int kInFrames = 1024;   // frames per capture buffer
constexpr int kInBuffers = 4;
constexpr int kSteps = 32;        // two bars of 16th notes
constexpr int kRows = 24;         // C3 .. B4
constexpr int kTopNote = 71;      // row 0 is B4
constexpr float kPi = 3.14159265358979f;

constexpr int kGridX = tok::kTrackW + tok::kKeysW;   // 226
constexpr int kGridY = tok::kTopH + tok::kRulerH;    // 76
constexpr int kClientW = kGridX + kSteps * tok::kCellW + 16;   // 1010
constexpr int kClientH = kGridY + kRows * tok::kCellH + tok::kStatusH;  // 500

constexpr int rowToMidi(int row) { return kTopNote - row; }

const char* const kNoteNames[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};
const char* const kKeyNames[12] = {"C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"};

struct ScaleDef {
    const char* name;
    std::vector<int> steps;   // semitones above the key
};
const ScaleDef kScales[4] = {
    {"Chromatic", {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}},
    {"Major", {0, 2, 4, 5, 7, 9, 11}},
    {"Minor", {0, 2, 3, 5, 7, 8, 10}},
    {"Pentatonic", {0, 3, 5, 7, 10}},
};

// ---------------------------------------------------------------- Pitch detection
constexpr int kWin = 1024;
constexpr int kMinLag = kSr / 1000;   // 1 kHz
constexpr int kMaxLag = kSr / 70;     // 70 Hz

// Normalized autocorrelation over a fixed 1024-sample frame. Scratch buffers are
// caller-owned so nothing is allocated on the audio thread.
float detectPitch(const float* x, double* E, double* r) {
    E[0] = 0.0;
    for (int i = 0; i < kWin; ++i) E[i + 1] = E[i] + double(x[i]) * double(x[i]);
    if (E[kWin] / kWin < 1e-5) return 0.f;  // silence gate

    for (int lag = kMinLag - 1; lag <= kMaxLag + 1; ++lag) {
        const int m = kWin - lag;
        double c = 0.0;
        for (int i = 0; i < m; ++i) c += double(x[i]) * double(x[i + lag]);
        const double denom = std::sqrt(E[m] * (E[kWin] - E[lag]));
        r[lag] = denom > 0.0 ? c / denom : 0.0;
    }

    double best = 0.0;
    for (int lag = kMinLag; lag <= kMaxLag; ++lag) best = std::max(best, r[lag]);
    if (best < 0.6) return 0.f;

    // Smallest near-peak lag avoids octave-down errors.
    int lag = kMinLag;
    while (lag <= kMaxLag && !(r[lag] >= 0.9 * best && r[lag] >= r[lag - 1] && r[lag] >= r[lag + 1])) ++lag;
    if (lag > kMaxLag) return 0.f;

    const double a = r[lag - 1], b = r[lag], c = r[lag + 1];
    const double d = a - 2.0 * b + c;
    const double shift = std::fabs(d) > 1e-12 ? 0.5 * (a - c) / d : 0.0;
    return static_cast<float>(kSr / (lag + shift));
}

float snapToScale(float midi, int key, int scaleIdx) {
    const std::vector<int>& steps = kScales[scaleIdx].steps;
    const int base = static_cast<int>(std::lround(midi));
    float best = midi;
    float bestDist = 1e9f;
    for (int d = -6; d <= 6; ++d) {
        const int note = base + d;
        const int pc = ((note - key) % 12 + 12) % 12;
        if (std::find(steps.begin(), steps.end(), pc) == steps.end()) continue;
        const float dist = std::fabs(float(note) - midi);
        if (dist < bestDist) {
            bestDist = dist;
            best = float(note);
        }
    }
    return best;
}

// ---------------------------------------------------------------- Real-time tuner
struct TuneParams {
    bool on;
    float strength;
    float speedMs;
    int key;
    int scaleIdx;
};

// Streaming pitch-synchronous overlap-add (PSOLA-style) pitch shifter.
//  - The source position follows real time, so the input is never consumed faster
//    than it arrives.
//  - Each grain is two detected periods long, centred on the nearest source mark
//    (marks advance one period per period of real time).
//  - Grains are spawned every period/ratio samples. Repeating the same source
//    segment at a tighter spacing is what raises the pitch, with no phase drift.
//  - Grains are normalised by 1/ratio so the overlap sum keeps unity gain.
//  - Latency is kLatency samples (about 46 ms).
class RealtimeTuner {
public:
    static constexpr int kLatency = 2048;  // must exceed the longest grain (2 * max period)
    static constexpr int kAnalysisHop = 512;
    static constexpr int kMaxGrains = 16;
    static constexpr size_t kRingSize = size_t(1) << 16;

    void reset() {
        ring_.fill(0.f);
        grains_ = {};
        offset_ = 0.f;
        detected_ = 0.f;
        period_ = 441.0;  // 100 Hz until the first detection
        markPos_ = -1.0;
        nextGrain_ = 0.0;
        wpos_ = 0;
    }

    float process(float x, const TuneParams& p) {
        ring_[idx(wpos_)] = x;
        if (wpos_ % kAnalysisHop == 0 && wpos_ >= kWin) analyze(p);

        const double ratio = std::pow(2.0, double(offset_) / 12.0);
        if (double(wpos_) >= nextGrain_) {
            spawn(1.0 / ratio);
            nextGrain_ += period_ / ratio;
            if (nextGrain_ < double(wpos_)) nextGrain_ = double(wpos_);
        }

        float y = 0.f;
        for (Grain& g : grains_) {
            if (!g.active) continue;
            const float w = 0.5f - 0.5f * std::cos(2.f * kPi * float(g.age) / float(g.len));
            y += g.gain * w * ring_[idx(g.src + g.age)];
            if (++g.age >= g.len) g.active = false;
        }
        ++wpos_;
        return y;
    }

    float detectedHz() const { return detected_; }

private:
    struct Grain {
        bool active;
        int age;
        int len;
        long long src;
        float gain;
    };

    // Two's-complement masking keeps negative (pre-start) indices inside the ring.
    static size_t idx(long long v) { return static_cast<size_t>(v) & (kRingSize - 1); }

    void spawn(double gain) {
        const double c = double(wpos_ - kLatency);  // real-time position in the input
        if (markPos_ < 0.0 || markPos_ > c + period_) markPos_ = c;
        while (markPos_ + 0.5 * period_ < c) markPos_ += period_;

        const int half = std::max(1, static_cast<int>(std::lround(period_)));
        for (Grain& g : grains_) {
            if (g.active) continue;
            g = Grain{true, 0, 2 * half, static_cast<long long>(std::llround(markPos_)) - half,
                      static_cast<float>(gain)};
            return;
        }
        // Pool full: drop the grain. At ratios up to 2 at most ~4 grains overlap.
    }

    void analyze(const TuneParams& p) {
        float frame[kWin];
        for (int i = 0; i < kWin; ++i) frame[i] = ring_[idx(wpos_ - kWin + 1 + i)];

        // Detection always runs so the period tracks the voice, even when tuning is off.
        detected_ = detectPitch(frame, E_.data(), R_.data());
        float want = 0.f;
        if (detected_ > 0.f) {
            period_ = double(kSr) / double(detected_);
            if (p.on) {
                const float midi = 69.f + 12.f * std::log2(detected_ / 440.f);
                const float target = snapToScale(midi, p.key, p.scaleIdx);
                want = std::clamp((target - midi) * p.strength, -12.f, 12.f);  // guard against glitches
            }
        }
        const float alpha =
            1.f - std::exp(-float(kAnalysisHop) / (std::max(1.f, p.speedMs) * 0.001f * float(kSr)));
        offset_ += (want - offset_) * alpha;
    }

    std::array<float, kRingSize> ring_{};
    std::array<Grain, kMaxGrains> grains_{};
    std::array<double, kWin + 1> E_{};
    std::array<double, kMaxLag + 2> R_{};
    float offset_ = 0.f;    // smoothed correction, semitones
    float detected_ = 0.f;  // last detected pitch, Hz
    double period_ = 441.0; // samples per period of the detected pitch
    double markPos_ = -1.0; // current source mark, absolute input index
    double nextGrain_ = 0.0;
    long long wpos_ = 0;
};

// ---------------------------------------------------------------- Synth
class Synth {
public:
    void noteOn(int note) {
        SynthVoice* v = nullptr;
        for (SynthVoice& candidate : voices_) {
            if (!candidate.active) {
                v = &candidate;
                break;
            }
        }
        if (!v) {  // steal round-robin
            v = &voices_[static_cast<size_t>(stealIdx_)];
            stealIdx_ = (stealIdx_ + 1) % kVoices;
        }
        v->active = true;
        v->gate = true;
        v->note = note;
        v->freq = 440.f * std::pow(2.f, float(note - 69) / 12.f);
    }

    void noteOff(int note) {
        for (SynthVoice& v : voices_)
            if (v.gate && v.note == note) v.gate = false;
    }

    void allOff() {
        for (SynthVoice& v : voices_) v.gate = false;
    }

    float render() {
        float out = 0.f;
        for (SynthVoice& v : voices_) {
            if (!v.active) continue;
            if (v.gate) {
                v.env = std::min(1.f, v.env + kAttack);
            } else {
                v.env -= kRelease;
                if (v.env <= 0.f) {
                    v.env = 0.f;
                    v.active = false;
                    continue;
                }
            }
            v.phase += v.freq / float(kSr);
            if (v.phase >= 1.f) v.phase -= 1.f;
            out += (2.f * v.phase - 1.f) * v.env;
        }
        return out * 0.12f;
    }

private:
    static constexpr int kVoices = 8;
    static constexpr float kAttack = 1.f / (0.005f * float(kSr));
    static constexpr float kRelease = 1.f / (0.25f * float(kSr));

    struct SynthVoice {
        bool active = false;
        bool gate = false;
        int note = -1;
        float freq = 0.f;
        float phase = 0.f;
        float env = 0.f;
    };

    std::array<SynthVoice, kVoices> voices_{};
    int stealIdx_ = 0;
};

// ---------------------------------------------------------------- Lock-free SPSC ring
class SpscRing {
public:
    static constexpr size_t kCap = size_t(1) << 16;

    void push(const float* s, size_t n) {
        size_t w = write_.load(std::memory_order_relaxed);
        const size_t r = read_.load(std::memory_order_acquire);
        for (size_t i = 0; i < n; ++i) {
            if (w - r >= kCap) break;  // full: drop the newest samples
            buf_[w & (kCap - 1)] = s[i];
            ++w;
        }
        write_.store(w, std::memory_order_release);
    }

    bool pop(float& out) {
        const size_t r = read_.load(std::memory_order_relaxed);
        if (r == write_.load(std::memory_order_acquire)) return false;
        out = buf_[r & (kCap - 1)];
        read_.store(r + 1, std::memory_order_release);
        return true;
    }

    void clear() { read_.store(write_.load(std::memory_order_acquire), std::memory_order_release); }

private:
    std::array<float, kCap> buf_{};
    std::atomic<size_t> write_{0};
    std::atomic<size_t> read_{0};
};

// ---------------------------------------------------------------- Engine
struct Snapshot {
    bool playing = false;
    bool micOn = false;
    bool tuneOn = false;
    bool synthMute = false;
    bool liveMute = false;
    bool hasNotes = false;
    bool faulted = false;
    int bpm = 120;
    int step = 0;
    int key = 0;
    int scaleIdx = 1;
    float detected = 0.f;
    float peak = 0.f;
    std::array<bool, kSteps * kRows> grid{};
    std::string status;
};

struct Engine {
    // Everything below the mutex is touched by the UI thread and/or audio thread.
    std::mutex mtx;

    // Transport and sequencer
    bool playing = false;
    int bpm = 120;
    int step = 0;
    double stepAcc = 0.0;
    std::array<bool, kSteps * kRows> grid{};
    std::vector<int> sounding;
    bool synthMute = false;
    bool liveMute = false;
    Synth synth;
    std::string status = "Ready. Press Play, or click the piano keys.";

    // Live input
    std::atomic<bool> micOn{false};
    std::atomic<bool> inFault{false};
    bool tuneOn = false;
    float strength = 1.f;
    float speedMs = 20.f;
    int key = 0;
    int scaleIdx = 1;
    RealtimeTuner tuner;
    SpscRing inRing;
    HWAVEIN hwi = nullptr;
    std::array<WAVEHDR, kInBuffers> inHdr{};
    std::array<std::array<int16_t, kInFrames>, kInBuffers> inData{};

    // Output
    HWAVEOUT hwo = nullptr;
    HANDLE evt = nullptr;
    std::thread audio;
    std::atomic<bool> running{false};
    std::atomic<bool> outFault{false};
    std::array<WAVEHDR, kOutBuffers> outHdr{};
    std::array<std::array<int16_t, kBlock>, kOutBuffers> outData{};
    std::atomic<float> peak{0.f};

    // Operations (UI thread)
    void togglePlay();
    void setBpm(int delta);
    void toggleCell(int col, int row);
    void clearGrid();
    void toggleLive();
    void toggleTune();
    void cycleKey();
    void cycleScale();
    void toggleSynthMute();
    void toggleLiveMute();
    void previewOn(int midi);
    void previewOff(int midi);
    void allNotesOff();
    Snapshot snapshot();

    // Lifecycle
    bool startOutput(std::string& err);
    void shutdown();

    // Audio thread
    void renderInto(std::array<int16_t, kBlock>& dst);

private:
    double samplesPerStep() const { return double(kSr) * 60.0 / (double(bpm) * 4.0); }
    TuneParams paramsLocked() const { return TuneParams{tuneOn, strength, speedMs, key, scaleIdx}; }
    void releaseAllLocked();
    void advanceStepLocked();
    bool startMicLocked(std::string& err);
    void stopMicLocked();
    void renderBlock(float* out);
};

Engine gEng;

// Defined later in the file; declared here so Engine methods can reference them.
void CALLBACK onWaveIn(HWAVEIN hw, UINT msg, DWORD_PTR inst, DWORD_PTR param1, DWORD_PTR reserved);
void audioLoop();

// ---- Engine: transport & sequencer
void Engine::releaseAllLocked() {
    for (int n : sounding) synth.noteOff(n);
    sounding.clear();
}

void Engine::advanceStepLocked() {
    releaseAllLocked();
    step = (step + 1) % kSteps;
    for (int r = 0; r < kRows; ++r) {
        if (grid[static_cast<size_t>(step * kRows + r)]) {
            const int n = rowToMidi(r);
            synth.noteOn(n);
            sounding.push_back(n);
        }
    }
}

void Engine::togglePlay() {
    std::lock_guard<std::mutex> lk(mtx);
    playing = !playing;
    if (playing) {
        step = kSteps - 1;
        stepAcc = samplesPerStep();  // first sample advances to step 0
        status = "Playing. Space stops.";
    } else {
        releaseAllLocked();
        status = "Stopped.";
    }
}

void Engine::setBpm(int delta) {
    std::lock_guard<std::mutex> lk(mtx);
    bpm = std::clamp(bpm + delta, 60, 200);
    status = "Tempo " + std::to_string(bpm) + " BPM.";
}

void Engine::toggleCell(int col, int row) {
    std::lock_guard<std::mutex> lk(mtx);
    const auto i = static_cast<size_t>(col * kRows + row);
    grid[i] = !grid[i];
}

void Engine::clearGrid() {
    std::lock_guard<std::mutex> lk(mtx);
    grid.fill(false);
    status = "Pattern cleared.";
}

void Engine::previewOn(int midi) {
    std::lock_guard<std::mutex> lk(mtx);
    synth.noteOn(midi);
}

void Engine::previewOff(int midi) {
    std::lock_guard<std::mutex> lk(mtx);
    synth.noteOff(midi);
}

void Engine::allNotesOff() {
    std::lock_guard<std::mutex> lk(mtx);
    releaseAllLocked();
    synth.allOff();
}

// ---- Engine: live input
void Engine::toggleLive() {
    std::lock_guard<std::mutex> lk(mtx);
    if (micOn.load()) {
        stopMicLocked();
        status = "Live input off. Nothing is being captured.";
        return;
    }
    std::string err;
    if (startMicLocked(err)) {
        status = "Live input on. Autotune is available. Latency is about 46 ms.";
    } else {
        status = err;
    }
}

void Engine::toggleTune() {
    std::lock_guard<std::mutex> lk(mtx);
    if (!micOn.load()) {
        status = "Turn on Live input before enabling Autotune.";
        return;
    }
    tuneOn = !tuneOn;
    status = tuneOn ? "Autotune on." : "Autotune off.";
}

void Engine::cycleKey() {
    std::lock_guard<std::mutex> lk(mtx);
    key = (key + 1) % 12;
    status = std::string("Key set to ") + kKeyNames[key] + ".";
}

void Engine::cycleScale() {
    std::lock_guard<std::mutex> lk(mtx);
    scaleIdx = (scaleIdx + 1) % 4;
    status = std::string("Scale set to ") + kScales[scaleIdx].name + ".";
}

void Engine::toggleSynthMute() {
    std::lock_guard<std::mutex> lk(mtx);
    synthMute = !synthMute;
    status = synthMute ? "Synth muted." : "Synth unmuted.";
}

void Engine::toggleLiveMute() {
    std::lock_guard<std::mutex> lk(mtx);
    liveMute = !liveMute;
    status = liveMute ? "Live channel muted." : "Live channel unmuted.";
}

bool Engine::startMicLocked(std::string& err) {
    WAVEFORMATEX fmt{};
    fmt.wFormatTag = WAVE_FORMAT_PCM;
    fmt.nChannels = 1;
    fmt.nSamplesPerSec = static_cast<DWORD>(kSr);
    fmt.wBitsPerSample = 16;
    fmt.nBlockAlign = 2;
    fmt.nAvgBytesPerSec = static_cast<DWORD>(kSr * 2);

    const MMRESULT rc = waveInOpen(&hwi, WAVE_MAPPER, &fmt, reinterpret_cast<DWORD_PTR>(onWaveIn), 0,
                                   CALLBACK_FUNCTION);
    if (rc != MMSYSERR_NOERROR) {
        hwi = nullptr;
        err = "No microphone available (device error " + std::to_string(rc) + ").";
        return false;
    }
    for (size_t i = 0; i < inHdr.size(); ++i) {
        WAVEHDR& h = inHdr[i];
        h = WAVEHDR{};
        h.lpData = reinterpret_cast<LPSTR>(inData[i].data());
        h.dwBufferLength = static_cast<DWORD>(kInFrames * 2);
        if (waveInPrepareHeader(hwi, &h, sizeof h) != MMSYSERR_NOERROR ||
            waveInAddBuffer(hwi, &h, sizeof h) != MMSYSERR_NOERROR) {
            err = "Microphone buffers could not be queued.";
            stopMicLocked();
            return false;
        }
    }
    inRing.clear();
    tuner.reset();
    inFault = false;
    micOn = true;
    if (waveInStart(hwi) != MMSYSERR_NOERROR) {
        micOn = false;
        stopMicLocked();
        err = "Microphone could not start.";
        return false;
    }
    return true;
}

void Engine::stopMicLocked() {
    micOn = false;
    tuneOn = false;
    if (!hwi) return;
    waveInStop(hwi);
    waveInReset(hwi);  // returns queued buffers; callback ignores them now that micOn is false
    for (WAVEHDR& h : inHdr) waveInUnprepareHeader(hwi, &h, sizeof h);
    waveInClose(hwi);
    hwi = nullptr;
}

// ---- Engine: audio rendering
void Engine::renderBlock(float* out) {
    std::lock_guard<std::mutex> lk(mtx);
    const double sps = samplesPerStep();
    float blockPeak = 0.f;
    for (int i = 0; i < kBlock; ++i) {
        if (playing) {
            stepAcc += 1.0;
            if (stepAcc >= sps) {
                stepAcc -= sps;
                advanceStepLocked();
            }
        }
        float s = synth.render();
        if (synthMute) s = 0.f;
        if (micOn.load()) {
            float in = 0.f;
            inRing.pop(in);
            const float wet = tuner.process(in, paramsLocked());
            if (!liveMute) s += wet;
        }
        out[i] = std::clamp(s * 0.8f, -1.f, 1.f);
        blockPeak = std::max(blockPeak, std::fabs(out[i]));
    }
    peak.store(blockPeak, std::memory_order_relaxed);
}

void Engine::renderInto(std::array<int16_t, kBlock>& dst) {
    std::array<float, kBlock> f{};
    renderBlock(f.data());
    for (size_t i = 0; i < kBlock; ++i) {
        dst[i] = static_cast<int16_t>(std::lrint(f[i] * 32767.f));
    }
}

// ---- Engine: output lifecycle
bool Engine::startOutput(std::string& err) {
    evt = CreateEventA(nullptr, FALSE, FALSE, nullptr);
    if (!evt) {
        err = "Could not create audio event.";
        return false;
    }
    WAVEFORMATEX fmt{};
    fmt.wFormatTag = WAVE_FORMAT_PCM;
    fmt.nChannels = 1;
    fmt.nSamplesPerSec = static_cast<DWORD>(kSr);
    fmt.wBitsPerSample = 16;
    fmt.nBlockAlign = 2;
    fmt.nAvgBytesPerSec = static_cast<DWORD>(kSr * 2);

    const MMRESULT rc = waveOutOpen(&hwo, WAVE_MAPPER, &fmt, reinterpret_cast<DWORD_PTR>(evt), 0, CALLBACK_EVENT);
    if (rc != MMSYSERR_NOERROR) {
        hwo = nullptr;
        err = "No audio output device (error " + std::to_string(rc) + ").";
        return false;
    }
    for (size_t i = 0; i < outHdr.size(); ++i) {
        WAVEHDR& h = outHdr[i];
        h = WAVEHDR{};
        h.lpData = reinterpret_cast<LPSTR>(outData[i].data());
        h.dwBufferLength = static_cast<DWORD>(kBlock * 2);
        waveOutPrepareHeader(hwo, &h, sizeof h);
        renderInto(outData[i]);  // prime so the first callbacks have data
        if (waveOutWrite(hwo, &h, sizeof h) != MMSYSERR_NOERROR) {
            err = "Audio output failed to start.";
            return false;
        }
    }
    running = true;
    audio = std::thread(audioLoop);
    return true;
}

void Engine::shutdown() {
    {
        std::lock_guard<std::mutex> lk(mtx);
        if (micOn.load()) stopMicLocked();
    }
    running = false;
    if (evt) SetEvent(evt);
    if (audio.joinable()) audio.join();
    if (hwo) {
        waveOutReset(hwo);
        for (WAVEHDR& h : outHdr) waveOutUnprepareHeader(hwo, &h, sizeof h);
        waveOutClose(hwo);
        hwo = nullptr;
    }
    if (evt) {
        CloseHandle(evt);
        evt = nullptr;
    }
}

Snapshot Engine::snapshot() {
    std::lock_guard<std::mutex> lk(mtx);
    Snapshot s;
    s.playing = playing;
    s.micOn = micOn.load();
    s.tuneOn = tuneOn;
    s.synthMute = synthMute;
    s.liveMute = liveMute;
    s.faulted = inFault.load() || outFault.load();
    s.bpm = bpm;
    s.step = step;
    s.key = key;
    s.scaleIdx = scaleIdx;
    s.detected = tuner.detectedHz();
    s.peak = peak.load(std::memory_order_relaxed);
    s.grid = grid;
    s.hasNotes = std::find(grid.begin(), grid.end(), true) != grid.end();
    s.status = status;
    return s;
}

// ---- Callbacks and audio loop
void CALLBACK onWaveIn(HWAVEIN hw, UINT msg, DWORD_PTR, DWORD_PTR param1, DWORD_PTR) {
    if (msg != WIM_DATA || !gEng.micOn.load()) return;
    auto* hdr = reinterpret_cast<WAVEHDR*>(param1);
    const size_t frames = std::min<size_t>(static_cast<size_t>(hdr->dwBytesRecorded) / sizeof(int16_t),
                                           size_t(kInFrames));
    std::array<float, kInFrames> f{};
    const auto* s = reinterpret_cast<const int16_t*>(hdr->lpData);
    for (size_t i = 0; i < frames; ++i) f[i] = static_cast<float>(s[i]) / 32768.f;
    gEng.inRing.push(f.data(), frames);
    if (waveInAddBuffer(hw, hdr, sizeof(WAVEHDR)) != MMSYSERR_NOERROR) gEng.inFault = true;
}

void audioLoop() {
    while (gEng.running.load()) {
        WaitForSingleObject(gEng.evt, 50);
        for (size_t i = 0; i < gEng.outHdr.size(); ++i) {
            WAVEHDR& h = gEng.outHdr[i];
            if ((h.dwFlags & WHDR_DONE) == 0) continue;
            gEng.renderInto(gEng.outData[i]);
            if (waveOutWrite(gEng.hwo, &h, sizeof h) != MMSYSERR_NOERROR) gEng.outFault = true;
        }
    }
}

// ---------------------------------------------------------------- UI state
enum BtnId : int {
    kBtnPlay,
    kBtnBpmDn,
    kBtnBpmUp,
    kBtnLive,
    kBtnTune,
    kBtnKey,
    kBtnScale,
    kBtnMuteSynth,
    kBtnMuteLive,
    kBtnClear,
    kBtnCount
};

std::array<RECT, kBtnCount> gBtn{};

void initLayout() {
    auto put = [](int id, int x, int y, int w, int h) { gBtn[static_cast<size_t>(id)] = RECT{x, y, x + w, y + h}; };
    put(kBtnPlay, 12, 10, 84, 32);
    put(kBtnBpmDn, 108, 10, 28, 32);
    put(kBtnBpmUp, 200, 10, 28, 32);
    put(kBtnLive, 240, 10, 96, 32);
    put(kBtnTune, 344, 10, 108, 32);
    put(kBtnKey, 460, 10, 76, 32);
    put(kBtnScale, 544, 10, 124, 32);
    put(kBtnMuteSynth, 110, 84, 50, 24);
    put(kBtnMuteLive, 110, 132, 50, 24);
    put(kBtnClear, 12, 186, 146, 28);
}

struct Ui {
    int hoverBtn = -1;
    int pressedBtn = -1;
    int hoverRow = -1;
    int hoverCol = -1;
    int previewRow = -1;
    bool tracking = false;
};
Ui gUi;

struct GdiRes {
    HFONT ui = nullptr;
    HFONT small = nullptr;
    HBRUSH bCanvas = nullptr, bSurface = nullptr, bRaised = nullptr, bHover = nullptr;
    HBRUSH bAccent = nullptr, bAccentPressed = nullptr, bDanger = nullptr;
    HBRUSH bKeyWhite = nullptr, bKeyBlack = nullptr, bBorder = nullptr;
    HPEN pBorder = nullptr, pAccent = nullptr;
};
GdiRes gdi;

void initGdi() {
    gdi.ui = CreateFontA(-16, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS,
                         CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, "Segoe UI");
    gdi.small = CreateFontA(-12, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS,
                            CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, DEFAULT_PITCH | FF_DONTCARE, "Segoe UI");
    gdi.bCanvas = CreateSolidBrush(tok::kCanvas);
    gdi.bSurface = CreateSolidBrush(tok::kSurface);
    gdi.bRaised = CreateSolidBrush(tok::kRaised);
    gdi.bHover = CreateSolidBrush(tok::kHover);
    gdi.bAccent = CreateSolidBrush(tok::kAccent);
    gdi.bAccentPressed = CreateSolidBrush(tok::kAccentPressed);
    gdi.bDanger = CreateSolidBrush(tok::kDanger);
    gdi.bKeyWhite = CreateSolidBrush(tok::kKeyWhite);
    gdi.bKeyBlack = CreateSolidBrush(tok::kKeyBlack);
    gdi.bBorder = CreateSolidBrush(tok::kBorder);
    gdi.pBorder = CreatePen(PS_SOLID, 1, tok::kBorder);
    gdi.pAccent = CreatePen(PS_SOLID, 1, tok::kAccent);
}

void freeGdi() {
    DeleteObject(gdi.ui);
    DeleteObject(gdi.small);
    for (HBRUSH b : {gdi.bCanvas, gdi.bSurface, gdi.bRaised, gdi.bHover, gdi.bAccent, gdi.bAccentPressed,
                     gdi.bDanger, gdi.bKeyWhite, gdi.bKeyBlack, gdi.bBorder})
        DeleteObject(b);
    DeleteObject(gdi.pBorder);
    DeleteObject(gdi.pAccent);
}

int buttonAt(int x, int y) {
    const POINT p{x, y};
    for (int i = 0; i < kBtnCount; ++i)
        if (PtInRect(&gBtn[static_cast<size_t>(i)], p)) return i;
    return -1;
}

bool gridCellAt(int x, int y, int& col, int& row) {
    if (x < kGridX || y < kGridY) return false;
    col = (x - kGridX) / tok::kCellW;
    row = (y - kGridY) / tok::kCellH;
    return col < kSteps && row < kRows;
}

bool keyColumnAt(int x, int y, int& row) {
    if (x < tok::kTrackW || x >= kGridX || y < kGridY) return false;
    row = (y - kGridY) / tok::kCellH;
    return row < kRows;
}

bool enabledOf(int id, const Snapshot& s) {
    if (id == kBtnTune) return s.micOn;
    if (id == kBtnClear) return s.hasNotes;
    return true;
}

bool toggledOf(int id, const Snapshot& s) {
    switch (id) {
        case kBtnPlay: return s.playing;
        case kBtnLive: return s.micOn;
        case kBtnTune: return s.tuneOn;
        case kBtnMuteSynth: return s.synthMute;
        case kBtnMuteLive: return s.liveMute;
        default: return false;
    }
}

std::string labelOf(int id, const Snapshot& s) {
    switch (id) {
        case kBtnPlay: return s.playing ? "Stop" : "Play";
        case kBtnBpmDn: return "-";
        case kBtnBpmUp: return "+";
        case kBtnLive: return s.micOn ? "Live: On" : "Live: Off";
        case kBtnTune: return s.tuneOn ? "Autotune: On" : "Autotune: Off";
        case kBtnKey: return std::string("Key: ") + kKeyNames[s.key];
        case kBtnScale: return std::string("Scale: ") + kScales[s.scaleIdx].name;
        case kBtnMuteSynth: return s.synthMute ? "Muted" : "Mute";
        case kBtnMuteLive: return s.liveMute ? "Muted" : "Mute";
        case kBtnClear: return "Clear pattern";
        default: return "";
    }
}

// ---------------------------------------------------------------- Painting
void drawText(HDC dc, RECT rc, const std::string& text, COLORREF color, HFONT font, UINT flags) {
    HGDIOBJ old = SelectObject(dc, font);
    SetTextColor(dc, color);
    DrawTextA(dc, text.c_str(), static_cast<int>(text.size()), &rc, flags);
    SelectObject(dc, old);
}

void fillRect(HDC dc, int l, int t, int r, int b, HBRUSH brush) {
    const RECT rc{l, t, r, b};
    FillRect(dc, &rc, brush);
}

void drawButton(HDC dc, int id, const Snapshot& s) {
    const RECT rc = gBtn[static_cast<size_t>(id)];
    const bool en = enabledOf(id, s);
    const bool tog = toggledOf(id, s);
    const bool hov = en && gUi.hoverBtn == id;
    const bool prs = en && gUi.pressedBtn == id;

    HBRUSH fill = gdi.bRaised;
    if (!en) fill = gdi.bSurface;
    else if (prs) fill = gdi.bAccentPressed;
    else if (hov) fill = gdi.bHover;

    SelectObject(dc, fill);
    SelectObject(dc, tog ? gdi.pAccent : gdi.pBorder);
    RoundRect(dc, rc.left, rc.top, rc.right, rc.bottom, tok::kRadius, tok::kRadius);

    const COLORREF text = !en ? tok::kTextDisabled : (tog ? tok::kAccent : tok::kText);
    drawText(dc, rc, labelOf(id, s), text, gdi.ui, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
}

void paintAll(HDC dc, int w, int h, const Snapshot& s) {
    SetBkMode(dc, TRANSPARENT);
    fillRect(dc, 0, 0, w, h, gdi.bCanvas);
    fillRect(dc, 0, 0, w, tok::kTopH, gdi.bSurface);

    for (int id = 0; id < kBtnCount; ++id) drawButton(dc, id, s);

    // BPM readout between the - and + buttons
    drawText(dc, RECT{140, 10, 196, 42}, std::to_string(s.bpm) + " BPM", tok::kText, gdi.ui,
             DT_CENTER | DT_VCENTER | DT_SINGLELINE);

    // Master meter and pitch readout
    drawText(dc, RECT{690, 8, 756, 26}, "Master", tok::kTextDim, gdi.small, DT_LEFT | DT_VCENTER | DT_SINGLELINE);
    const RECT meter{762, 13, 962, 25};
    fillRect(dc, meter.left, meter.top, meter.right, meter.bottom, gdi.bCanvas);
    FrameRect(dc, &meter, gdi.bBorder);
    const int fillW = static_cast<int>(std::clamp(s.peak, 0.f, 1.f) * 198.f);
    fillRect(dc, 763, 14, 763 + fillW, 24, s.peak > 0.95f ? gdi.bDanger : gdi.bAccent);
    char pitchBuf[48];
    if (s.micOn && s.detected > 0.f)
        std::snprintf(pitchBuf, sizeof pitchBuf, "Input pitch %.0f Hz", static_cast<double>(s.detected));
    else
        std::snprintf(pitchBuf, sizeof pitchBuf, "Input pitch: none");
    drawText(dc, RECT{690, 30, 990, 48}, pitchBuf, tok::kTextDim, gdi.small, DT_LEFT | DT_VCENTER | DT_SINGLELINE);

    // Track list
    fillRect(dc, 0, kGridY, tok::kTrackW, kGridY + 44, gdi.bSurface);
    drawText(dc, RECT{12, kGridY + 6, 105, kGridY + 26}, "Synth", tok::kText, gdi.ui,
             DT_LEFT | DT_VCENTER | DT_SINGLELINE);
    drawText(dc, RECT{12, kGridY + 26, 105, kGridY + 42}, "Piano roll", tok::kTextDim, gdi.small,
             DT_LEFT | DT_VCENTER | DT_SINGLELINE);
    fillRect(dc, 0, kGridY + 48, tok::kTrackW, kGridY + 92, gdi.bSurface);
    drawText(dc, RECT{12, kGridY + 54, 105, kGridY + 74}, "Live vocal", tok::kText, gdi.ui,
             DT_LEFT | DT_VCENTER | DT_SINGLELINE);
    const char* liveSub = !s.micOn ? "Input off" : (s.tuneOn ? "Autotune on" : "Input on");
    drawText(dc, RECT{12, kGridY + 74, 105, kGridY + 90}, liveSub, tok::kTextDim, gdi.small,
             DT_LEFT | DT_VCENTER | DT_SINGLELINE);

    // Ruler
    fillRect(dc, kGridX, tok::kTopH, w, kGridY, gdi.bSurface);
    for (int col = 0; col < kSteps; col += 4) {
        const int x = kGridX + col * tok::kCellW;
        drawText(dc, RECT{x + 4, tok::kTopH, x + 40, kGridY}, std::to_string(col / 4 + 1), tok::kTextDim,
                 gdi.small, DT_LEFT | DT_VCENTER | DT_SINGLELINE);
    }

    // Piano keys and grid
    for (int row = 0; row < kRows; ++row) {
        const int y = kGridY + row * tok::kCellH;
        const int midi = rowToMidi(row);
        const int pc = midi % 12;
        const bool black = pc == 1 || pc == 3 || pc == 6 || pc == 8 || pc == 10;

        HBRUSH keyBrush = black ? gdi.bKeyBlack : gdi.bKeyWhite;
        if (gUi.previewRow == row) keyBrush = gdi.bAccent;
        fillRect(dc, tok::kTrackW, y, kGridX, y + tok::kCellH, keyBrush);
        if (pc == 0) {
            const std::string name = std::string(kNoteNames[pc]) + std::to_string(midi / 12 - 1);
            drawText(dc, RECT{tok::kTrackW + 4, y, kGridX - 4, y + tok::kCellH}, name,
                     black ? tok::kText : tok::kKeyBlack, gdi.small, DT_RIGHT | DT_VCENTER | DT_SINGLELINE);
        }

        fillRect(dc, kGridX, y, w, y + tok::kCellH, black ? gdi.bSurface : gdi.bCanvas);
        for (int col = 0; col < kSteps; ++col) {
            const int x = kGridX + col * tok::kCellW;
            const bool on = s.grid[static_cast<size_t>(col * kRows + row)];
            HBRUSH f = nullptr;
            if (on) f = gdi.bAccent;
            else if (gUi.hoverRow == row && gUi.hoverCol == col) f = gdi.bHover;
            else if (s.playing && col == s.step) f = gdi.bRaised;
            if (f) fillRect(dc, x + 1, y + 1, x + tok::kCellW - 1, y + tok::kCellH - 1, f);
        }
    }
    // Bar separators
    for (int col = 0; col < kSteps; col += 4)
        fillRect(dc, kGridX + col * tok::kCellW, kGridY, kGridX + col * tok::kCellW + 1, kGridY + kRows * tok::kCellH,
                 gdi.bBorder);

    // Status bar
    const int sy = h - tok::kStatusH;
    fillRect(dc, 0, sy, w, h, gdi.bSurface);
    const std::string msg = s.faulted ? std::string("Audio device stopped unexpectedly. Turn Live input off and on.")
                                      : s.status;
    drawText(dc, RECT{12, sy, w - 12, h}, msg, s.faulted ? tok::kDanger : tok::kTextDim, gdi.small,
             DT_LEFT | DT_VCENTER | DT_SINGLELINE);
}

// ---------------------------------------------------------------- Input handling
void activate(HWND hwnd, int id) {
    switch (id) {
        case kBtnPlay: gEng.togglePlay(); break;
        case kBtnBpmDn: gEng.setBpm(-1); break;
        case kBtnBpmUp: gEng.setBpm(1); break;
        case kBtnLive: gEng.toggleLive(); break;
        case kBtnTune: gEng.toggleTune(); break;
        case kBtnKey: gEng.cycleKey(); break;
        case kBtnScale: gEng.cycleScale(); break;
        case kBtnMuteSynth: gEng.toggleSynthMute(); break;
        case kBtnMuteLive: gEng.toggleLiveMute(); break;
        case kBtnClear:
            if (MessageBoxA(hwnd, "Clear every note in the synth pattern? This can't be undone.", "Clear pattern",
                            MB_YESNO | MB_ICONQUESTION) == IDYES)
                gEng.clearGrid();
            break;
        default: break;
    }
}

// Piano keys mapped to one octave starting at C3 (row for MIDI 48).
int pianoOffset(WPARAM vk) {
    static constexpr char kKeys[] = "ZSXDCVGBHNJM";
    for (int i = 0; i < 12; ++i)
        if (vk == static_cast<WPARAM>(kKeys[i])) return i;
    return -1;
}

LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
        case WM_TIMER:
            InvalidateRect(hwnd, nullptr, FALSE);
            return 0;

        case WM_ERASEBKGND:
            return 1;

        case WM_PAINT: {
            PAINTSTRUCT ps{};
            HDC dc = BeginPaint(hwnd, &ps);
            RECT rc{};
            GetClientRect(hwnd, &rc);
            const int w = rc.right;
            const int h = rc.bottom;
            HDC mem = CreateCompatibleDC(dc);
            HBITMAP bmp = CreateCompatibleBitmap(dc, w, h);
            HGDIOBJ old = SelectObject(mem, bmp);
            paintAll(mem, w, h, gEng.snapshot());
            BitBlt(dc, 0, 0, w, h, mem, 0, 0, SRCCOPY);
            SelectObject(mem, old);
            DeleteObject(bmp);
            DeleteDC(mem);
            EndPaint(hwnd, &ps);
            return 0;
        }

        case WM_MOUSEMOVE: {
            const int x = static_cast<short>(LOWORD(lp));
            const int y = static_cast<short>(HIWORD(lp));
            if (!gUi.tracking) {
                TRACKMOUSEEVENT tme{sizeof tme, TME_LEAVE, hwnd, 0};
                TrackMouseEvent(&tme);
                gUi.tracking = true;
            }
            gUi.hoverBtn = buttonAt(x, y);
            int col = -1, row = -1;
            if (gridCellAt(x, y, col, row)) {
                gUi.hoverCol = col;
                gUi.hoverRow = row;
            } else {
                gUi.hoverCol = -1;
                gUi.hoverRow = -1;
            }
            InvalidateRect(hwnd, nullptr, FALSE);
            return 0;
        }

        case WM_MOUSELEAVE:
            gUi.tracking = false;
            gUi.hoverBtn = -1;
            gUi.hoverRow = -1;
            gUi.hoverCol = -1;
            InvalidateRect(hwnd, nullptr, FALSE);
            return 0;

        case WM_LBUTTONDOWN: {
            const int x = static_cast<short>(LOWORD(lp));
            const int y = static_cast<short>(HIWORD(lp));
            SetCapture(hwnd);
            const int b = buttonAt(x, y);
            int row = -1, col = -1;
            if (b >= 0) {
                gUi.pressedBtn = b;
            } else if (keyColumnAt(x, y, row)) {
                gUi.previewRow = row;
                gEng.previewOn(rowToMidi(row));
            } else if (gridCellAt(x, y, col, row)) {
                gEng.toggleCell(col, row);
            }
            InvalidateRect(hwnd, nullptr, FALSE);
            return 0;
        }

        case WM_LBUTTONUP: {
            const int x = static_cast<short>(LOWORD(lp));
            const int y = static_cast<short>(HIWORD(lp));
            if (gUi.previewRow >= 0) {
                gEng.previewOff(rowToMidi(gUi.previewRow));
                gUi.previewRow = -1;
            }
            if (gUi.pressedBtn >= 0) {
                const int pressed = gUi.pressedBtn;
                gUi.pressedBtn = -1;
                ReleaseCapture();
                if (buttonAt(x, y) == pressed) activate(hwnd, pressed);
            } else {
                ReleaseCapture();
            }
            InvalidateRect(hwnd, nullptr, FALSE);
            return 0;
        }

        case WM_KEYDOWN: {
            if ((lp & (LPARAM(1) << 30)) != 0) return 0;  // ignore auto-repeat
            switch (wp) {
                case VK_SPACE: gEng.togglePlay(); break;
                case 'L': gEng.toggleLive(); break;
                case 'T': gEng.toggleTune(); break;
                case VK_OEM_PLUS:
                case VK_ADD: gEng.setBpm(1); break;
                case VK_OEM_MINUS:
                case VK_SUBTRACT: gEng.setBpm(-1); break;
                default: {
                    const int off = pianoOffset(wp);
                    if (off >= 0) gEng.previewOn(48 + off);
                    break;
                }
            }
            InvalidateRect(hwnd, nullptr, FALSE);
            return 0;
        }

        case WM_KEYUP: {
            const int off = pianoOffset(wp);
            if (off >= 0) gEng.previewOff(48 + off);
            return 0;
        }

        case WM_KILLFOCUS:
            gEng.allNotesOff();
            return 0;

        case WM_DESTROY:
            KillTimer(hwnd, 1);
            gEng.shutdown();
            freeGdi();
            PostQuitMessage(0);
            return 0;

        default:
            return DefWindowProcA(hwnd, msg, wp, lp);
    }
}

}  // namespace

int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int nShow) {
    initLayout();
    initGdi();

    WNDCLASSA wc{};
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.hCursor = LoadCursorA(nullptr, IDC_ARROW);
    wc.lpszClassName = "WorkshopDaw";
    if (!RegisterClassA(&wc)) {
        freeGdi();
        return 1;
    }

    RECT frame{0, 0, kClientW, kClientH};
    AdjustWindowRect(&frame, WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX, FALSE);
    HWND hwnd = CreateWindowExA(0, "WorkshopDaw", "Workshop DAW", WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX,
                                CW_USEDEFAULT, CW_USEDEFAULT, frame.right - frame.left, frame.bottom - frame.top,
                                nullptr, nullptr, hInst, nullptr);
    if (!hwnd) {
        freeGdi();
        return 1;
    }

    std::string err;
    if (!gEng.startOutput(err)) {
        gEng.status = err;
    }

    SetTimer(hwnd, 1, 33, nullptr);  // ~30 fps repaint for playhead and meter
    ShowWindow(hwnd, nShow);
    UpdateWindow(hwnd);

    MSG msg{};
    for (;;) {
        const BOOL got = GetMessageA(&msg, nullptr, 0, 0);
        if (got <= 0) break;
        TranslateMessage(&msg);
        DispatchMessageA(&msg);
    }
    return static_cast<int>(msg.wParam);
}
