# Backend Decoupling — CureIR narrow waist & portable process algebra

STATUS: PARKED / FORWARD-LOOKING. Filed 2026-07-14. Not scheduled; captured so the
design survives context resets. Follow-up to the `actor`/`fsm`/`sup`/`app`
macro work (importable BEAM concurrency over the sealed `Std.Otp.Raw` algebra).

Companion doctrine: `2026-07-13-cure-evidential-systems-architecture.md` — that
document is the *safety rail* for everything here (see "Why the doctrine matters"
below). This spec is the concrete multi-backend plan; that one is the discipline
that keeps multi-backend from becoming a soundness disaster.


## Goal

Let Cure compile to targets other than the BEAM — LLVM IR / C / Rust / JS / WASM
— without wedding the language, and especially the guarantees, to any one VM.
Gleam is the shape-of-the-thing reference (BEAM + JS dual target), with one
critical caveat learned from it (below).


## The core thesis: the macro work decouples SYNTAX, not SEMANTICS

Making `actor`/`fsm`/`sup`/`app` importable removes them from the kernel and the
surface grammar. Necessary, but it is **step 1 of ~3**. What those imports expand
to is still `spawn`/`receive`/`link`/`monitor`/selective-receive/supervision —
i.e. BEAM process semantics. Syntax is portable; meaning is still 100% BEAM.

The real decoupling is one level down:

    actor/fsm/sup MUST be expressed against an ABSTRACT process/mailbox/
    supervisor EFFECT INTERFACE that admits more than one lawful implementation.

This is Part V of the evidential-systems spec (runners §38 interpreting an effect
interface; effect specifications §43). The existing `typed-beam-process-algebra`
(BEAM/OTP as a typed algebra over a sealed raw base, `Std.Otp.Raw`) is the SEED:
the move is to generalize "sealed over raw BEAM" into "an interface of which BEAM
is ONE implementation."


## The honest fork

### Value fragment — easy, high value
Total dependent functions erase to plain functional code that lowers to
LLVM/C/Rust/JS/WASM without drama. Worth doing on its own: Cure-verified logic in
a browser or as a native lib, zero BEAM dependency. This is the part of
"like Gleam" that works cleanly.

### Process fragment — hard, semantically lossy (the Gleam caveat)
Gleam compiles to BEAM AND JS, but `gleam/otp` is **BEAM-only**. On JS you get
functions and a different concurrency story: no actors, no preemption, no
isolated per-process heaps, no supervision-as-runtime. Gleam did not port OTP to
JS because **OTP _is_ the runtime**. Reimplementing faithful BEAM process
semantics on another target means becoming a BEAM-runtime author (cf. Lumen,
which died on exactly this).

Consequence — scope honestly:

- A non-BEAM process target means "**we ship a per-target scheduler/runtime**,"
  NOT "it just works."
- The **guarantees differ per target**. A mailbox-bound proof under
  `BEAMMailboxModel` is NOT valid under a JS cooperative event loop. This is
  evidential-systems §130 ("AtomVM MUST NOT inherit BEAM/ERTS certificates by
  analogy") generalized to every backend.


## Why the doctrine matters (the safety rail)

Multi-backend done carelessly silently transports BEAM-proved properties
(mailbox bounds, restart semantics, fairness) onto targets where they are false.
The evidential-systems doctrine is the fix, and makes this initiative *cheap*
w.r.t. the TCB:

- §118 relational compilation — each lowering is a RELATION with its forward
  compiler / validator / lifter claimed separately. Adding a backend = adding a
  relation, not weakening a claim.
- §72 BEAM trust split + §151 observer-indexed compatibility — every claim names
  its target model; `TimingCompatible`-on-BEAM ≠ `TimingCompatible`-on-native and
  the compiler KNOWS it.
- §7 — the kernel contains NO codegen/scheduling/backends.

Architectural gift: **multi-backend is TCB-cheap as long as it lives BELOW the
canonical-erased-core waist.** The elaborator emits erased Core; backends consume
it; the kernel never learns what an `i32` is. It turns dangerous only if a backend
concern leaks UP into typing (e.g. "this type means a machine word on the C
target"). Keep the waist clean → adding targets is purely additive.

NON-NEGOTIABLE: this entire initiative must be invisible to the kernel/TCB.


## Architecture: the narrow-waist IR

Cure's dependent Core is too rich to be the multi-target waist. Erase first to a
small UNTYPED FUNCTIONAL IR ("CureIR"), then fan out. Classic move (GHC:
Core→STG→Cmm).

    Surface → dependent Core → (erase) → CureIR → { BEAM/CoreErlang, LLVM, C, JS/WASM }
                                            └─ the narrow waist; backends see ONLY this

CureIR is post-erasure, untyped-or-minimally-typed, functional. It is the single
place every backend attaches. The process algebra appears in CureIR as calls
against the abstract process/mailbox/supervisor interface — each backend supplies
the runner.


## Sequencing (defended order)

1. **Effect-interface abstraction** for `actor`/`fsm`/`sup`: macros → interface
   over an abstract process algebra. This is the REAL decoupling; everything else
   is blocked on it. (Generalize `Std.Otp.Raw` from sealed-BEAM to an interface.)
2. **Define CureIR** (post-erasure IR) and re-target the EXISTING BEAM path
   through it first — prove the waist loses nothing on the backend we already
   have before adding new ones.
3. **Value-only second target** (LLVM or JS): no processes, proves the fan-out,
   immediately useful (browser/native pure logic).
4. **Process runtime per non-BEAM target**: scoped explicitly as "ship a
   scheduler"; guarantees RE-DERIVED under that target's model, never inherited.


## Open design question (raised, not resolved)

Should `fsm` go through the SAME process interface as `actor`, or a more
RESTRICTED one? An `fsm` is a total transition function + state, driven by a
loop — it does not need raw `spawn`/arbitrary-`receive` power. A restricted
"driven transition" interface is likely far easier to port (it maps to a plain
event loop on JS, a poll loop in C) than general actors. This suggests a LADDER
of process interfaces (fsm ⊂ actor ⊂ raw) where lower rungs port to more targets
and carry stronger portable guarantees. Decide before step 1 locks the interface
shape.


## Non-goals / cautions

- NOT reimplementing full OTP semantics on every target. Per-target runtimes may
  legitimately offer weaker/different concurrency models.
- NOT letting backend ambition pull the kernel around (§7).
- NOT transporting any BEAM-modelled guarantee to another target without
  re-deriving it under that target's named model.
