# Antigen V2 — Unifier Soundness — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot via `/loop` (autonomous continuation)

Third phase of the untrusted-machinery initiative (task #66), after V3 and V1. Tests
the two **untrusted** unification engines against the trusted kernel: `Cure.Elab.Unify`
(Core terms + metavariables — feeds elaboration) and `Cure.Types.Unify` (surface
types — solves implicit arguments). No `Cure.Core.*`/`Cure.Elab.*`/`Cure.Types.*`
edits, no `:meck`, no new dependency.

## The design crux — two oracle situations, one vertical

The two engines are one vertical but differ in whether an external oracle exists,
driving a two-family split (fixed at spec time, hardened by both reviews):

- **V2a — `Elab.Unify`** works on Core terms, where the trusted `Cure.Core.Conv` is
  a **genuine external oracle**. → a real **differential**: if
  `unify(t1,t2,ctx,sig) = {:ok, ctx'}`, then `zonk(t1,ctx')` and `zonk(t2,ctx')`
  must be `Conv`-convertible. This checks *here* the soundness the engine's own
  δ-fallback moduledoc only waves at ("a wrong accept is caught downstream").
- **V2b — `Types.Unify`** works on surface types with **no external equality** (it
  accepts non-syntactic matches: `:any`, `int`/`float` widening, refinement-strip,
  named↔record/adt). → **intrinsic laws + a fixpoint self-consistency** proxy
  (re-unify the substituted sides ⟹ no new bindings), the oracle-free tactic V1c used.

## What shipped — four assays

| id | engine | property | oracle |
|---|---|---|---|
| `unify/soundness` | `Elab.Unify` | zonked sides `Conv`-equal | `Conv` |
| `unify/intrinsic` | `Elab.Unify` | occurs / idempotent-zonk / meta-closed | none |
| `unify_types/fixpoint` | `Types.Unify` | re-unify substituted = no new bindings | none |
| `unify_types/intrinsic` | `Types.Unify` | occurs / idempotent-apply / var-elim | none |

Plus `Antigen.Generators.UnifyProblem` (fixed catalogs, closed ctor-only Core terms
for V2a; surface types exercising every non-syntactic accept for V2b) and
`assay_module/1` dispatch for the four ids.

## Result of running it

**Both engines are sound on the whole catalog** — every soundness, intrinsic, and
fixpoint entry re-checks clean under the real ops (Task 5's "whole catalog" test is
green). No infection surfaced; the **eight** negative controls prove the assays are
load-bearing: wrong-ctor solve, meta-survived success, cyclic `eu_solution`,
non-idempotent zonk, identity zonk (V2a); dropped-binding solve, cyclic-accept,
leaky `apply_subst`, wrapping `apply_subst` (V2b) are each caught.

## Two design refinements found while grounding (plan-time)

1. **Split op-map for the fixpoint control** (`tu_unify` solve + `tu_reunify`
   re-check, both real by default). A *systematically*-buggy unifier used for BOTH
   the solve and the re-check is self-consistent — its bug is "stable" — so the
   fixpoint negative control only bites when the re-check stays real and rediscovers
   the dropped binding (`s' != s`).
2. **Occurs helper reads `eu_solution` once, then walks structurally** — following
   solutions recursively would infinite-loop on the cyclic-`eu_solution` stub.

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Spec | V2 two-family design written | `<spec>` |
| 1 — Spec review (Sonnet) | 10 passes; **added a closedness precondition** to V2a (`Conv.conv?(_,_,[],0,_)` needs closed terms); fixed a vacuous/false meta-closed property (reviewer caught its own false "every meta solved" fix mid-loop); simplified metavar threading to literal `{:meta,N}` | `b60000a` |
| 2 — Plan | 6-task TDD plan (2 reconciliations: split op-map, single-level occurs) | `a84cca1` |
| 3 — Plan review (Sonnet) | 6 passes; **added 4 negative controls** for previously-untested violation branches (dead-code risk); overturned my `occurs_raw?` compile-risk note (empirically fine); added non-emptiness asserts | `bd3521e` |
| 4 — Execute (Opus, TDD) | red → green per task, ghost-authored | `bb4b801`, `8507e8d`, `e5405b4`, `6c2c61a`, `bba9429` |
| 5 — Verify | full suite green; quarantine clean | (this report) |

### Per-task execution (Stage 4)

1. **`bb4b801`** — `unify/soundness` + `run/2` seam + local `meta_free?/1`. Green 4/4.
2. **`8507e8d`** — `unify/intrinsic` (occurs via single-level `eu_solution` + idempotent zonk + meta-closed). Green 8/8.
3. **`e5405b4`** — `unify_types/fixpoint` (split `tu_reunify`). Green 10/10.
4. **`6c2c61a`** — `unify_types/intrinsic` (`%{expect: :error}` clause first + `has_solved_var?`). Green 14/14.
5. **`bba9429`** — `UnifyProblem` catalogs + dispatch + `:unify_problem` kind. Green 16/16 — whole catalog clean.

## Verification

- **Full suite (single authorized run):** `2679 passed` (3 doctests, 2676 tests),
  0 failures — +16 from V1's 2663.
- **StreamData quarantine:** `architecture_test.exs` green (no literal `StreamData`
  token in the assay — V1's Stage-5 lesson held; the constraint was pre-banked in
  the spec/plan and never tripped).
- **Working tree:** clean (test-run seed side-effect reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Boundaries

V2 **finds** unsound unification; it does not fix any (none surfaced). Curated
fixed catalog, not a random unify-problem fuzzer. V2a's closed-term differential
does **not** cover genuine free-variable re-levelling under a solved meta (that
needs an open term under an ambient context, which `Conv.conv?(_,_,[],0,_)` cannot
validly compare — an accepted first-cut gap, not to be worked around by relaxing
closedness). `Types.Unify` has no external oracle by design (intrinsic + fixpoint
only). No higher-order/Miller unification. No determinism assay (both engines are
pure over explicit state — a same-inputs check would be tautological). No SMT (V6).

## Next phases (umbrella roadmap, task #66)

- **V5 totality-closure**, then **V4 erasure/relevance**, then **V6 SMT lint**.

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
