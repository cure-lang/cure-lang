# Antigen V1 — Normalizer Soundness — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot via `/loop` (autonomous continuation)

Second phase of the untrusted-machinery initiative (task #66), after V3. Tests the
**untrusted** type-level normalizer `Cure.Types.Reduce` — the definitional-equality
engine the type checker uses before falling back to SMT — against the **trusted**
`Cure.Core` kernel. Three assays; no `Cure.Core.*`/`Cure.Types.*` edits, no `:meck`,
no new dependency.

## What shipped — three assays

- **`normalizer/differential` (V1a):** `Reduce.normalize(ast, bindings)`'s output,
  translated to Core, must be `Conv`-equal to the kernel normal form of an
  **independently-encoded** equivalent term. The independence is the crux (see
  below).
- **`normalizer/equal` (V1b) — the soundness property:** `Reduce.equal?(a,b)`
  returning `true` while the kernel finds `a`,`b` **not** convertible is an unsound
  definitional-equality discharge (`{:equal_unsound,…}`) — it would admit an
  ill-typed program, exactly like an SMT false discharge. Soundness-only by design
  (a false `false` is a reach gap, out of scope).
- **`normalizer/intrinsic` (V1c):** on the **untranslatable** fragment (where
  `CoreBridge.to_core → :error` and `structural_congruence` governs, so no oracle
  exists), two intrinsic laws — `normalize` is a fixpoint (idempotence) and never
  grows the term (monotone size, a literal moduledoc guarantee). Per the operator's
  open-Q2 resolution to cover the untranslatable fragment.

Plus `Antigen.Generators.SurfaceExpr` (fixed catalogs + the independent `encode/2`)
and `assay_module/1` dispatch for the three ids.

## The independence crux (spec review, Stage 1)

The original differential re-derived its "oracle" by calling `CoreBridge.to_core`
on the **same** AST `Reduce.normalize` uses internally — so a `to_core`
mistranslation was invisible (identical on both sides), and with `bindings = %{}`
it never exercised `do_substitute` (real production code: `Types.Pi`,
`Types.Dependent`). The review restructured V1a/V1b so the generator builds
`{ast, bindings, core_expected}` triples where `core_expected` comes from a
**second, independently-written surface→Core encoder** (`SurfaceExpr.encode/2`)
with bindings folded in — so a bridge or substitution bug now surfaces as a real
mismatch, not a mirrored one. The substitution negative control (Task 1 test 3)
pins exactly this.

## Result of running it

**`Types.Reduce` is sound on the whole catalog** — every differential, equal, and
intrinsic entry re-checks clean under the real kernel (Task 4's "whole catalog"
test is green). No infection surfaced; the five negative controls prove the assays
are load-bearing (corrupted read-back, dropped substitution, untranslatable result,
unsound `equal?=true`, non-idempotent/size-growing congruence are each caught).

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Spec | V1 design written | `9fcdbd4` |
| 1 — Spec review (Sonnet) | 6 passes; **fixed a circular/vacuous differential** (independent encoder) + Conv API conflation + softened V1c idempotence claim | `7683289` |
| 2 — Plan | 5-task TDD plan (2 reconciliations: fixed-catalog, code-under-test op-map) | `88a142e` |
| 3 — Plan review (Sonnet) | 3 passes; **fixed a test-invalidating surface-vs-core op-name bug** (`:+` vs `:add` — kernel folds only core names) + 3 more | `a119a8d` |
| 4 — Execute (Opus, TDD) | red → green per task, ghost-authored | `dd5765e`, `f18fcea`, `582ef60`, `fa762ee` |
| 5 — Verify | full suite; fixed one quarantine trip (see below) | (in `fa762ee`) |

### Per-task execution (Stage 4)

1. **`dd5765e`** — `normalizer/differential` assay + `run/2` seam. Green 4/4.
2. **`f18fcea`** — `normalizer/equal` soundness. Green 6/6.
3. **`582ef60`** — `normalizer/intrinsic` (size-first cond, `term_size/1`). Green 9/9.
4. **`fa762ee`** — `SurfaceExpr` catalogs + dispatch + `:surface_expr` kind. Green 11/11 — whole catalog clean.

## Two review stages both caught test-invalidating defects

This vertical is a case study in why the review loop is worth its cost:
- **Stage 1** caught a **circular differential** — the test would have been vacuous
  (a `to_core` bug invisible, `do_substitute` never exercised).
- **Stage 3** caught a **surface-vs-core operator-name mismatch** — the plan's
  hand-written `{:prim, :+, …}` core literals would never fold (`Eval.fold` keys on
  `:add`), so the `:ok`-asserting baseline tests would have failed against a correct
  assay. Fixed by routing all core terms through the independent `encode/2`.

## Verification

- **Full suite (single authorized run + one re-run after the quarantine fix):**
  `2663 passed` (3 doctests, 2660 tests), 0 failures — +11 from V3's 2652.
- **StreamData quarantine:** `architecture_test.exs` green. (Stage 5's first run
  tripped it — the `SurfaceExpr` moduledoc contained the literal word "StreamData"
  in a comment, and the guard is a literal grep over `generators/`+`assays/`.
  Reworded; re-run green. Folded into `fa762ee`.)
- **Working tree:** clean (test-run seed side-effect reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Boundaries

V1 **finds** unsound/incorrect normalization; it does not fix any (none surfaced).
It runs a curated fixed catalog (elab pattern), not a random surface-expr fuzzer —
a generator-expansion follow-on could widen coverage. `equal?` is checked
soundness-only (a false `false` reach gap is out of scope). No SMT (that is V6);
V1 is the pre-SMT definitional-equality layer.

## Next phases (umbrella roadmap, task #66)

- **Phase 3 — V2 unifier** covering **both** `Elab.Unify` and `Types.Unify`.
- Then V5 totality-closure, V4 erasure/relevance, V6 SMT lint.

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
