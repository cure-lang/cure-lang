# `gates` — Digital Logic for Teaching and Bench Work

**Date:** 2026-07-08
**Status:** design. Child of
[`2026-07-08-beginner-embedded-surfaces-design.md`](2026-07-08-beginner-embedded-surfaces-design.md)
(idea backlog #95, promoted); built as a `macro` (§5), zero compiler
special-casing. The four hiding principles (§3) are law.

---

## 1. Purpose

Combinational and sequential digital logic — truth tables, gate netlists,
Karnaugh-map-style minimization — for CS/electronics learners meeting
Boolean algebra AND bench tinkerers wiring real 74xx chips. The audiences
meet in the bench harness (§5): the declaration that teaches the theory
verifies the solder. `gates` is also the **third audience for the causality
theorem**, after `flow` and `synth`: a combinational loop — an output
feeding back to an input with no flip-flop in the path — is rejected by the
same causality index those macros carry; the user hears only "real
hardware would oscillate" (§3).

## 2. Surface

Three declaration forms: `truth` (a function by truth table), `circuit` (a
gate netlist), and `register` elements inside circuits (flip-flops).

```cure
truth Majority(a, b, c) -> out
  0 0 0 -> 0
  0 0 1 -> 0
  0 1 0 -> 0
  0 1 1 -> 1
  1 0 0 -> 0
  1 0 1 -> 1
  1 1 0 -> 1
  1 1 1 -> 1

circuit MajorityGates implements Majority
  in  a, b, c
  out out
  wire ab = and(a, b)
  wire bc = and(b, c)
  wire ac = and(a, c)
  out <- or(ab, or(bc, ac))
```

Sequential circuits add `register` — a D flip-flop with a clock and an
optional clear line:

```cure
circuit Counter2
  in  clk, reset
  out %[q1, q0]                  # LSB-first pair; buses are ledgered (§9.2)
  register q0 = not(q0)     on clk, clear reset
  register q1 = xor(q1, q0) on clk, clear reset
```

Surface rules: a `truth` table lists every row exactly once (violations
named at elaboration; don't-care outputs are `x` and free the minimizer).
The gate vocabulary is the classic seven (`and`, `or`, `not`, `nand`,
`nor`, `xor`, `xnor`), fixed in v1. Every wire has exactly one driver — a
second driver is a domain error ("that's a short circuit"), never a
unification dump. `register q = expr on clk` latches at the clock edge; `q`
may appear in its own expression — feedback *through* the flip-flop is
legal (§3). `implements` is checked at compile time (§4).

Invisible machinery: wires are values of a two-point type; a circuit
elaborates to a total function (combinational) or a `reducer`-shaped step
function (sequential) with the causality index manufactured from the
netlist's wire graph. Users write gates; the macro writes types.

## 3. Causality — combinational loops

The netlist's dependency graph must be acyclic *through combinational
elements*. A `register` is a delay element: its output this tick is a
function of *last* tick's inputs, so it breaks a cycle. This is precisely
`flow`'s decoupledness rule and `synth`'s unit-delay rule — the same
causality index, discharged structurally; nothing surfaces.

```
error[E240]: this loop has no flip-flop
  --> latch.cure:4
   |
 4 |  wire x = nand(x, y)
   |       ^ x depends on itself through gates only
  Real hardware would oscillate — a wire can't depend on itself in the
  same instant. Put a register in the loop: register x = nand(x, y) on clk
```

The sequential rule, stated the way `synth` states it: **a flip-flop IS
the delay that makes feedback legal.** `Counter2` compiles because its
loops pass through registers. Same theorem, same explainer shape, third
domain.

## 4. Equivalence checking

`implements` obligations are discharged **exhaustively**: enumerate every
input vector, evaluate the netlist, compare against the table. This domain
lives at small n by design — the honest bound is **16 inputs** (65,536
vectors, negligible at compile time). Beyond it the declaration is
rejected, and the message says why: enumeration past 2^16 stops being
teaching and starts being synthesis — split the circuit into implementable
sub-blocks; this tool keeps circuits small on purpose (§10).

A failed check reports the exact disagreeing vector in truth-table
vocabulary (§6). Sequential circuits have no finite input enumeration:
`implements` is combinational-only; bounded-sequence conformance is §7's.

## 5. The bench harness — the killer feature

From a `circuit` plus a board declaration, `gates` generates an **ESP32
GPIO test harness** that drives the real chips on your breadboard through
every input combination and verifies outputs against the compile-time truth
table. Spec meets solder: **your homework is checked against physics.**

```cure
bench MajorityBench
  board  :esp32c3
  checks MajorityGates
  chip u1: :sn74hc08             # quad 2-input AND
  chip u2: :sn74hc32             # quad 2-input OR
  drive a -> pin.gpio4, b -> pin.gpio5, c -> pin.gpio6
  sense out <- pin.gpio7
```

The flashed harness walks all 8 vectors, settles, samples, and reports over
serial. Mismatches speak electronics:

```
bench MajorityBench: 7/8 vectors pass
  ✗ with A=1 B=0, pin 6 reads LOW, expected HIGH — check the pull-down
    on pin 3, and that u2 pin 14 actually has 3.3V on it.
```

- **Wiring map generated** — which GPIO drives which DIP pin, from chip
  pinout + netlist. The `wiring` idea's territory (backlog #1); kept
  minimal here — a table, not a diagram.
- **Electrical safety is a v1 check, not a ledger item** — it is a
  refinement, and refinements are what we do. Chip families declare
  supply/logic levels (`:sn74hc*` 2–6 V; `:sn74ls*` 5 V TTL); the harness
  checks the board's GPIO voltage capability against the declared family
  at compile time — sensing a 5 V LS output with a 3.3 V-only ESP32 pin
  fails before flashing ("use an HC chip at 3.3V, or a level shifter").
- The harness settles generously between vectors — breadboard propagation
  is microseconds, the harness waits milliseconds, so the zero-delay model
  (§9.1) is safe on real chips.

Also generated, from the same declarations: **simulation functions** (pure
Cure — the circuit runs in `check`, in `cure run --sim`, anywhere a
function does); **waveform diagrams** for sequential circuits (timing-free
unit-delay ticks — the classroom artifact for `Counter2`); and **minimized
forms** (the K-map result shown next to the original — "your circuit uses
6 gates; 4 suffice: out = ab + bc + ac"). Minimization is a teaching
artifact, never a rewrite — the netlist is what gets checked and benched.

## 6. Explainers

Per the parent's error-explainer architecture (§4) — raw kernel vocabulary
reaching a `gates` user is a defect by definition. The flagship is the loop
error (§3); the other signature shape is the equivalence counterexample:

```
error[E242]: MajorityGates differs from the truth table Majority
  --> majority.cure:12
  At A=1, B=1, C=0: the circuit gives 0, the table says 1.
  Trace: ab=1, bc=0, ac=0 — the discrepancy is upstream of `out`.
```

Fan-out warnings (one output driving more inputs than the family's rating —
a real bench failure mode) are wanted but ledgered (§9.5): they need
per-family electrical data v1 chip declarations may not carry.

## 7. `check` integration

- **Equivalence is static discharge.** An `implements` obligation reports
  as `proved (exhaustive — 8 vectors)`: enumeration at small n is the
  discharge-by-computation rung, with the vector count as receipt.
- **Sequential templates.** Macro-shipped bounded-sequence templates:
  reset behavior (registers cleared after any sequence ending in `reset`),
  counter rollover (`Counter2` back to `%[0, 0]` after 4 ticks), "registers
  only change on clock edges". Bounded model checking, never called that.
- **The bench harness IS `check` on-device.** The check spec ledgers
  on-device property runs over the serial harness as deferred
  ([`2026-07-08-check-macro-design.md`](2026-07-08-check-macro-design.md)
  §10.8); `gates` is its **concrete pilot** — the first on-device check
  story. The property is the truth table, the generator is exhaustive
  enumeration, the system under test is silicon, and the per-vector report
  is the serial-harness protocol that spec can later generalize. Pass/fail
  arrives over serial, never assumed (repo rule).

## 8. Relations

- **`automata`** (backlog #25, teaching family, homed with sim/pattern):
  the FSM ↔ sequential-circuit correspondence is a teaching bridge both
  macros present — a DFA compiles to registers + next-state logic; a
  `gates` sequential circuit *is* a Moore machine.
- **`board` / `driver` / `wiring`**: the harness consumes `board`'s typed
  pins (drive needs `output`, sense needs `input` — literal discharge);
  chip pinouts are `driver`-adjacent data; the full physical surface is
  `wiring`'s.
- **`lesson`**: the curriculum host — `gates` supplies the logic-design
  chapters (truth tables → K-maps → circuits → the bench day).
- **`flow`**: the same causality index proves `flow` graphs free of
  instantaneous feedback — one theorem, shared.
- **`synth`**: states the unit-delay-legalizes-feedback rule first;
  `gates`' flip-flop rule is its verbatim sibling.
- **`ladder`** (backlog #96): the industrial cousin — PLC ladder logic at
  relay scale.

## 9. Open decisions (ledger)

1. **Propagation-delay modeling** — v1 is the zero-delay ideal (gates
   instantaneous, registers unit delays); timing and glitch/hazard
   analysis are honest future work, ledgered rather than promised.
2. **Bus / multi-bit notation** — wire vectors (`in a[4]`), the `%[q1, q0]`
   pairing formalized. Probably v1.5: the teaching arc hits 4-bit adders
   fast, but scalar wires keep v1 small.
3. **HDL export** — Verilog for the student moving on to FPGA tooling.
   Someday; the netlist is already the right data.
4. **Chip-family library scope** — which 74xx parts ship pinout +
   electrical declarations in v1; packaged like boards? (Voltage checking
   itself is decided: v1, §5.)
5. **Fan-out warnings** — per-family drive/load data (§6); decide the
   declaration surface and whether v1 chips carry it.
6. **Open-collector / tristate** — wired-AND buses, pull-up requirements,
   the one-driver rule's principled exception. Real 74xx territory; not v1.
7. **Deliberate latches** — SR-latch-from-gates is a classic lesson but a
   causality violation as written (§3); a marked latch-intent surface, or
   teach it with `register` primitives?

## 10. Non-goals

- **No FPGA synthesis** — no mapping, placement, or optimization targets;
  export (§9.3) hands off to real tools.
- **No analog simulation** — no SPICE, no voltage curves; the harness's
  electrical checks are refinements, not circuit simulation.
- **No timing closure** — zero-delay ideal plus generous bench settling;
  setup/hold analysis means you have outgrown the tool.
- **No big circuits** — the 16-input equivalence bound is a feature: n
  stays small by design, and the error message says so out loud (§4).
