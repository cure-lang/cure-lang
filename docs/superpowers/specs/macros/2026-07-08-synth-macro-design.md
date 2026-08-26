# `synth` — Modular-Synthesizer Patch Graphs

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #33, promoted); built as a `macro` (§5), zero compiler
special-casing. The four hiding principles (§3) are law: no user ever sees an
index or a kernel error. Closest sibling:
[`pattern`](2026-07-08-sim-pattern-macro-design.md) — same demographic,
same OSC-out architecture, same Erlang-timing pedigree.

---

## 1. Purpose

`synth` declares a modular-synthesizer patch — oscillators, filters,
envelopes, VCAs, LFOs, delays, and the cables between them — checked the way
a real rack punishes you: an undelayed feedback loop is rejected at compile
time, a control cable in an audio jack is a type error in musician
vocabulary, an unwired filter input is caught before a note plays.

The design's reason to exist is one sentence: **"a feedback loop without a
delay element is rejected" is *literally the same causality index* the Safe
FRP Types work builds for `flow`.** One theorem, new audience. In `flow` it
reads as "your dataflow cannot deadlock"; in `synth` it reads as "your patch
can't blow up your speakers." No new machinery: the causality/decoupledness
indices live in the reactive-runtime design bible (v12); `synth` merely
points them at a patch graph. This is `fleet`'s purity-dividend story with a
different coin — the **causality dividend** (§3).

## 2. Surface

Modules are declared, then wired in an indentation-structured `patch` block.
A cable is `producer.port -> consumer.port`; ports are typed by **signal
kind** (audio, control, gate/trigger) **and rate** (§4).

```cure
use Play.Synth

synth Acid
  voice mono

  module osc1 = saw(freq: 110hz)
  module lfo1 = lfo(sine, rate: 0.5hz)
  module env1 = adsr(attack: 5ms, decay: 120ms, sustain: -6db, release: 200ms)
  module vcf  = lowpass(cutoff: 800hz, resonance: 0.7)
  module fb   = delay(time: 250ms, feedback: 0.4)
  module amp  = vca()

  patch
    osc1.out   -> vcf.in
    lfo1.out   -> vcf.cutoff          # control-rate cable onto a control port
    env1.out   -> amp.gain
    vcf.out    -> amp.in
    amp.out    -> fb.in
    fb.out     -> vcf.in              # feedback path — legal: fb IS a delay
    amp.out    -> main.out

  on gate ->
    env1.trigger
```

Surface rules:

- **`module name = ctor(params)`** instantiates from the module library
  (oscillators, filters, envelopes, LFOs, VCAs, mixers, delays, S&H,
  sequencers). Parameters carry units (§4); a bare number where a unit
  belongs is the units macro's error, inherited for free.
- **`patch`** holds cables. One producer may feed many consumers (a mult is
  just multiple arrows from one port); an input port takes exactly one
  cable — mixing is explicit via `mixer(n)`, exactly as on a real rack.
- **`voice mono`** in v1; polyphony/voice allocation is ledgered (§9.1).
- **`on gate` / `on note(..)`** clauses receive performance events (from
  `pattern`, MIDI when it lands, or GPIO triggers) and poke module inputs.
- Required inputs left unwired are a compile error (§6); optional modulation
  inputs (e.g. `vcf.cutoff`) have declared defaults.

Under the hood a patch is a Flow graph — modules are signal functions,
cables are edges — which is what makes §3 free.

## 3. The causality dividend

Every modular tutorial warns about the same accident: close a feedback loop
with no delay and the "signal" is an instantaneous algebraic constraint, not
a process — real hardware resolves it as a scream at full amplitude. The
Safe-FRP causality/decoupledness index (the design bible's theorem;
positioning only, not respecified here) makes exactly this distinction: a
feedback edge is well-formed **iff the loop passes through a decoupled
node** — one whose output *now* does not depend on its input *now*. In
synthesis vocabulary, decoupled nodes are exactly the modules with
memory-across-time: `delay`, and anything built on one.

So the check costs nothing new: a `patch` block elaborates onto Flow, and
the existing index either discharges (every cycle crosses a delay) or fails
as §6's feedback error — never as an index. The `fb.out -> vcf.in` cable in
§2 is legal *because* `fb` is a `delay`; remove `fb` from the loop and the
same cable is rejected with the fix named.

## 4. Rate discipline

Control rate and audio rate are **distinct clock domains**, and ports carry
their domain in the type:

- **`Audio`** ports — per-sample signals. The BEAM never computes these
  (§5); an audio cable is an *edge in the graph we hand to the backend*.
- **`Control`** ports — LFOs, envelopes, sequencer steps, knob values;
  computed and scheduled by the BEAM on the tempo/control clock.
- **`Gate` / `Trigger`** ports — edge-shaped control events.

Connecting an audio-rate output to a control-rate input (or vice versa)
requires an explicit converter — Eurorack's audio-vs-CV distinction, typed:

- `a2k(source, window: 10ms)` — audio → control: envelope-follow/downsample
  (audio is too fast for a control input; say how to summarize it).
- `k2a(source, slew: 5ms)` — control → audio: upsample with slew
  (a raw control step at audio rate is a click; say how to smooth it).

A rate mismatch without a converter is a type error with a friendly
explainer (§6). Units ride the units macro throughout — `hz`, `db`, `st`
(semitones), `samples`: `osc1.freq + 7` does not compile,
`osc1.freq |> up(7st)` does. The ms/µs bug class, killed the same way.

## 5. Backends & the honesty boundary

Stated plainly, because everything else here depends on it: **the BEAM does
control-rate work superbly and does not do per-sample audio DSP.** Not a
limitation to apologize for — it is Sonic Pi's actual, proven architecture:
an Erlang timing core driving an external synthesis engine — we keep the
split. The macro owns the **patch graph** (module topology, port/rate/unit
types, the causality check — all compile-time) and the **control signals**
(LFOs, envelope schedules, sequencer clocks, parameter automation — BEAM-side
on the Flow runtime, at control rate). The backend owns per-sample DSP:

1. **SuperCollider over OSC (v1)** — the same output decision as `pattern`'s
   v1 (`out osc("localhost", 57120)`): a patch compiles to synth
   instantiation + parameter-set messages, control signals stream as
   timestamped OSC bundles. SynthDef vs. stock synths: ledgered (§9.5).
2. **On-device codec/DAC NIFs (ledgered, §9.3)** — I2S codec boards exist
   for ESP32; per-sample DSP would run in C NIFs, the BEAM still doing only
   control.

**The on-device crossover that works today** is not audio at all — it is
**control voltage**. The eurorack-DIY / hardware-synth crowd overlaps
heavily with the MCU audience (the same people own soldering irons *and*
patch cables) and wants CV and gates from an ESP32: the same patch algebra
with `main.out` replaced by DAC/PWM sinks through `board`/`driver`
(`out cv(dac1)`, `out gate(pin.gpio5)`). LFOs, envelopes, quantized
sequencers — all control-rate, all BEAM-native, driving physical control
voltages into real analog hardware. Write the modulation brain in Cure; let
the rack make the sound.

Hot-swap rides the toolchain REPL / hot code push exactly as `pattern` does
(its §3.2): re-patch live, cables swap at the next control-clock boundary; a
push that fails the causality or rate check changes nothing — the old patch
keeps sounding.

## 6. Explainers

Per the parent's error-explainer architecture (§4); raw kernel vocabulary
(the causality index especially) reaching a `synth` user is a defect.

```
error[E205]: this feedback path has no delay element
  --> acid.cure:21
   |
21 |     amp.out -> vcf.in
   |     ^^^^^^^^^^^^^^^^^
  amp.out already depends on vcf.out in this same instant — the loop
  amp -> vcf -> amp closes with zero delay. Real hardware would scream.
  Put a delay module in the loop:
      amp.out -> fb.in
      fb.out  -> vcf.in        # fb = delay(time: ..) breaks the instant

error[E206]: audio-rate signal patched into a control-rate input
  --> acid.cure:17
  vcf.out is an audio signal; lfo2.rate is a control input — far too slow
  to follow audio. If you want the loudness contour, follow the envelope:
      a2k(vcf.out, window: 10ms) -> lfo2.rate

error[E207]: filter `vcf` has nothing wired to its input
  --> acid.cure:9
  A filter with no input is silence with extra steps. Patch a source into
  vcf.in — e.g. osc1.out -> vcf.in — or delete the module.
```

(E206's mirror — control into an audio input — suggests `k2a(.., slew: ..)`
and names the click it prevents.)

## 7. `check` integration

Macro-shipped templates (parent §7.5 — "your macros write your tests"),
run against the compiled control graph — and, for audio laws, the backend's
rendered output where the sim harness supports it.

```cure
check AcidLaws
  ## Patch algebra: a linear chain (no generators inside) maps silence to
  ## silence — a patch that hums with no input has a bug.
  prop silence_in_silence_out(chain: LinearChain(Acid)) =
    render(chain, input: silence, dur: 1s) == silence

  ## Mixer inputs commute — channel order is not part of the sound.
  prop mixer_commutes(m: Mixer(2), a: ControlSeq, b: ControlSeq) =
    render(m, %[in(0) <- a, in(1) <- b], dur: 1s)
      == render(m, %[in(0) <- b, in(1) <- a], dur: 1s)

  ## Same seed ⇒ same LFO phases, envelope timings, sequencer steps.
  prop control_reproducible(seed: Nat) =
    control_trace(Acid, seed, dur: 8s) == control_trace(Acid, seed, dur: 8s)
```

Static discharge applies: "no feedback loop is undelayed" reports *proved by
construction* — it is §3's theorem, not a test — and reproducibility may
too (control scheduling is deterministic, by `sim`'s lockstep argument).

## 8. Relations

- **`pattern`** — the natural upstream: patterns drive synth parameters and
  gates on the shared tempo clock (`play bass |> into(Acid.note)`); a live
  set is `pattern` for *when*, `synth` for *what*. Same OSC transport.
- **`flow`** — the substrate: a patch *is* a Flow graph; the causality index
  is shared, not duplicated (§3).
- **units** — Hz/dB/semitones/samples are ordinary literal rules (§4).
- **`board`/`driver`** — CV/gate sinks on DAC/PWM pins (§5); codec drivers
  for the on-device DSP future.
- **`fleet`** — a distributed patch across devices is projection of a patch
  graph; one ledger line (§9.7), not a v1 promise.
- **Toolchain REPL** — hot-swap (§5) is a hard dependency, shared with
  `pattern`; if it slips, live re-patching slips.

## 9. Open decisions (ledger)

1. **Polyphony / voice allocation** — v1 is `voice mono`. `voice poly(8)`:
   is voice stealing a typestate discipline (a stolen voice's release is a
   tracked state) or a policy knob; oldest / quietest / released-first?
2. **MIDI in** — host-side first (a MIDI event stream feeding `on note`);
   DIN/TRS MIDI on ESP32 UART is plausible and this crowd will ask week one.
3. **On-device DSP via codec NIFs** — scope + chip set (I2S: ES8388,
   PCM5102-class); NIF-backed module subset vs. SC-only; Cure or community?
4. **Preset / patch storage** — a `schema` for saved patches (modules +
   cables + parameters), so presets get typed migration like any store.
5. **SynthDef generation vs. stock synths** — compile the patch graph to a
   generated SuperCollider SynthDef (faithful topology) or map modules onto
   a curated stock-synth bank (sounds in minute one). Likely: stock bank v1,
   SynthDef generation as the fidelity upgrade.
6. **Converter defaults** — blessed `a2k`/`k2a` window/slew defaults so
   beginners can write `a2k(x)`, or force the parameter (honest teaching)?
7. **Distributed patches over `fleet`** — CV brain on one node, modulation
   on another; revisit once both macros have real users.
8. **Visual patch editor via `blocks`** — a cable graph is the most visual
   surface in the catalog; owned by the `blocks` effort.

## 10. Non-goals

- **No in-BEAM per-sample DSP** — timing and control in the BEAM, samples in
  the synth engine (§5); the proven Sonic Pi split, same stance as `pattern`.
- **No DAW ambitions** — patching and performance, not arrangement, mixing,
  or editing.
- **No audio plugin formats** — no VST/AU/CLAP hosting or export; the
  backend boundary is OSC and (eventually) NIFs, nothing else.
