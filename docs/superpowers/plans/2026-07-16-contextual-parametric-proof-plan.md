# Plan — retire `contextual` on parametric-erased `beam_ops` rules (gate a)

> **STATUS: EXECUTED 2026-07-16 (`a543cfb9`).** Landed for `beam_ops self` (the
> only nullary all-erased-implicit `beam_ops` rule). Full suite 4237 passed,
> Antigen 318/318, TCB delta zero. Deviations from the plan below, all
> simplifications: (1) Task 3 (distinct `:proven_parametric` manifest status)
> was DROPPED — parametric acceptance is a genuine well-typedness proof (the term
> is well-typed at a schematic type, unsolved only in erased/irrelevant
> positions), so a plain `:passed` is honest and no manifest surgery was needed.
> (2) The predicate reads the callee key straight from the
> `{:unsolved_metavariables, name}` error (the elaborator already resolves it), so
> no name-resolution step was required. (3) Guards are unit-tested by exposing the
> pure `parametric_erased_call?/3` — a relevant-implicit behavioral negative is
> unauthorable (implicits are erased-by-default; a nullary relevant-explicit call
> just partial-applies), so direct predicate unit tests are the faithful check.
> (4) Only `self` qualified; every other `beam_ops` rule supplies arguments and
> stays `contextual` by design (intrinsically use-site-bound, not a gap).

**Branch:** `core-let-binder` (accumulating stack). Work in the worktree root
`.claude/worktrees/core-let-binder`, never the parent clone.

**Status of the surrounding programme (verified 2026-07-16):** the macro facility
host spine is complete + green; the generic-unix AtomVM runtime gate passes for all
eight OTP surfaces (`atomvm_container_test.exs`, `--include atomvm`, 1 passed).
This plan closes the LAST host-testable gate before the REMAINING-WORK §8 DONE bar:
the SP3 *generative* self-proof still EXEMPTS the `contextual` `beam_ops`
expression rules, so "generatively proven to expand to well-typed Core" is not yet
literally met for them. The remaining gate after this one is ESP32 hardware
(operator-driven). This slice is OPTIONAL polish — the rules are already checked at
real use sites — but it is the maximal autonomous host completion.

## Problem (ground truth)

`beam_ops self contextual becomes Std.Otp.self()` (`lib/std/otp.cure:13`) is
exempted from the SP3 proof by `contextual` (consumed at `macro_fuzz.ex:360,374`).
Without the exemption the proof runs `check_expression_expansion`
(`macro_fuzz.ex:505`) → `Elaborator.elaborate_expr_typed(expansion, [],
Context.empty(env), env)` → fails `{:unsolved_metavariables, :"Std.Otp#self"}`,
because `self : {m: Type} -> Effect(Pid(m))` (`otp.cure:116`) has an erased result
index `m` with nothing to solve against use-site-free. The two producers of that
error (`elaborator.ex:6727` ctor-app, `:7500` global-app) carry ONLY the callee
name — not which args/erasure — so we do NOT change them (blast radius: ~15
`{:unsolved_metavariables, _}` matchers).

## Approach (chosen: narrow parametric-erased acceptance in the PROOF harness only)

Sound because an ERASED index is computationally irrelevant: if the expansion
elaborates for a fresh/arbitrary instantiation of an unconstrained erased index, it
is well-typed for ALL instantiations by parametricity. The proof harness can decide
this from the callee's signature WITHOUT the partial term:

- `implicit_def?(env, name)` (`elaborator.ex:2292`) already reports whether a def's
  quantities contain `:erased`; `Env.get_def(env, name)` exposes `%{quantities: q}`.
- The safe, decidable subset: a contextual EXPRESSION rule whose expansion is a
  direct application of a global `name` where **every** parameter of `name` is an
  erased implicit AND the expansion supplies **no explicit argument** (nullary /
  all-implicit application, e.g. `Std.Otp.self()`). Then the only unsolved
  metavariables are exactly `name`'s erased implicits → accept as
  *proven-parametrically*. This covers the `beam_ops self`-shaped rules; it does
  NOT cover hole-carrying rules (fsm.cure, `tell`/`stop` with typed pids), which
  stay `contextual` and out of scope here.

Rejected alternatives (recorded, do not redo): (A) enrich the elaborator error
contract to surface residual metavars + erasure — larger blast radius, no new
capability we need here; (B) per-rule declared expected-type surface — adds
user-facing macro surface the operator has DEFERRED. This narrow harness rule needs
neither.

## Tasks (strict red-green; scoped `mix test` only, full suite once at the gate)

### Task 1 — helper `parametric_erased_proof?/3` (RED first)
- RED: add `test/cure/compiler/macro_parametric_proof_test.exs` asserting a new
  `Cure.Compiler.MacroFuzz`-level predicate accepts the `Std.Otp.self()` expansion
  (all-erased-implicit nullary global) and REJECTS (a) a global with a relevant
  (non-erased) unsolved param, (b) an application supplying explicit args, (c) a
  non-application expansion. Use the real `Std.Otp` env (the test helper already
  compiles the stdlib).
- GREEN: implement `parametric_erased_proof?(expansion, env, name)`: match the
  expansion as a direct global application (surface `{:function_call, …}` /
  `{:app, …}` — verify the actual expansion shape of `Std.Otp.self()` first with a
  probe), look up `Env.get_def(env, resolved_name)`, confirm the telescope is
  non-empty and every param is an erased implicit, and that no explicit arg is
  supplied. Pure function; no elaborator change.

### Task 2 — wire into `check_expression_expansion` (RED first)
- RED: extend the Task-1 test (or a sibling) to assert that
  `check_expression_expansion(:self, input, self_expansion, env)` returns `:ok`
  after wiring (currently returns `{:error, {:expansion_ill_typed, …}}`).
- GREEN: in `check_expression_expansion` (`macro_fuzz.ex:505`), on `{:error,
  {:unsolved_metavariables, name}}`, return `:ok` iff `parametric_erased_proof?`.
  Keep every other error path unchanged.

### Task 3 — honest manifest status (RED first)
- RED: assert the per-rule manifest entry for a parametric-accepted rule carries a
  DISTINCT status (e.g. `:proven_parametric`), not a plain `:passed`, so the
  weaker guarantee is not misreported as full proof.
- GREEN: thread the status through `cached_proof`'s manifest builder
  (`macro_fuzz.ex:354`). `:deferred` (contextual) disappears for these rules,
  replaced by `:proven_parametric`.

### Task 4 — drop `contextual` from the qualifying rules
- Remove `contextual` ONLY from the `beam_ops` expression rules that are
  all-erased-implicit nullary globals (audit each in `otp.cure`; `self` at :13 is
  the exemplar — enumerate the rest and confirm each qualifies by signature).
  LEAVE `contextual` on hole-carrying / value-relevant rules and all `fsm.cure`
  rules. For any `beam_ops` rule that does NOT qualify, keep `contextual` and note
  why in a comment.
- Scoped `mix test test/cure/compiler/macro_fuzz_test.exs` (or the SP3 proof test)
  green after each removal.

### Gate
- Full `mix test` once, alone: expect the prior 4235-green plus the new tests, 0
  failures. Antigen suite green. Then update the state doc CURRENT POSITION: gate
  (a) CLOSED, only ESP32 hardware remains before §8 DONE.

## Constraints
TCB delta ZERO (no `lib/cure/core/*`). Ghost commits
(`--author="Made In Heaven <madeinheaven@madeinheaven.com>"`, no co-sign).
Explicit pathspec only. Tests immutable once green. If any qualifying-rule removal
turns the full suite red for a reason NOT covered by `parametric_erased_proof?`,
STOP and re-scope — do not broaden the acceptance predicate to force green.
