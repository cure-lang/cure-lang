# Antigen V3 — Elaborator Soundness — Completion Report

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot (design-approved gate → hands-off)

First phase of the untrusted-machinery initiative (task #66). Closes the
highest-value gap outside the kernel TCB: the **untrusted elaborator emits core
terms that nothing trusted ever re-checks**. The new `elab/soundness` assay makes
the trusted kernel independently re-derive the type of every core definition the
elaborator produces and confirm it matches the emitted type — so an elaborator
that *accepts* a program but emits ill-typed core (bad de Bruijn index,
mis-inserted implicit, wrong type annotation) is now caught. Pure-Antigen, kernel
+ elaborator reached read-only; **no `Cure.Core.*`/`Cure.Elab.*` edits, no
`:meck`, no new dependency.**

## The property

For a construction-guaranteed well-typed surface program, if
`Program.elaborate(src) = {:ok, env}`, then every function def in `env.defs` must
independently type-check under the kernel: `Kernel.infer(ctx, core)` succeeds and
its type is `Conv`-equal to the emitted type — with a `Kernel.check` fallback for
checking-mode-only forms (parameter-bearing constructor bodies), and every per-def
check fuel-bounded at the committed `500_000` floor. Infection classes:
`{:core_ill_typed, name, e}`, `{:type_annotation_wrong, name, …}`,
`{:elaborator_raised, id, e}`, `{:fuel_exhausted, name}`.

## What shipped

- **`elab/soundness` assay** (new clauses in `Antigen.Assays.Elab`) with a `run/2`
  injectable op-map seam (`elaborate/infer/check/conv/eval`) mirroring Run C's
  pattern — the only injection path for the negative controls, no TCB touch.
- **Decision procedure** — `infer`→`Conv` with a `check`-fallback triggered by the
  kernel's own `{:error, {:ctor_requires_checking_mode, _}}` signal (single source
  of truth, covers any non-inferable former); hole-bearing bodies skipped;
  every check wrapped in `Normalise.with_fuel(500_000, …)` so a non-normalizing
  emitted def reports `:fuel_exhausted` instead of hanging the run.
- **Generator + wiring** — `ElabComplete.soundness_challenges/0` re-tags the
  completeness catalog; `assay_module("elab/soundness")` dispatches it. Follows the
  elab family's established fixed-catalog pattern (not `default_gen`).

## Result of running it

**The elaborator is sound on the entire completeness catalog** — every emitted
core def re-checks clean under the real kernel (Task 4's "whole catalog"
test is green). No unsound-elaboration infection surfaced; the three negative
controls prove the assay *would* catch one (ill-typed core, mistyped
parameter-bearing constructor, non-normalizing core are each caught).

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| — Decisions | umbrella open-questions resolved (V3 leads, intrinsic untranslatable assay, V2 = both unifiers) | `0b29154` |
| 0 — Spec | V3 design written | `9938734` |
| 1 — Spec review (Sonnet) | 5 passes; 3 substantive fixes (ctor `check` exception, `Conv` fuel bound, `elaborate` in the seam) | `ec4709e` |
| 2 — Plan | 5-task TDD plan | `1326df7` |
| 3 — Plan review (Sonnet) | 3 passes; 4 fixes (MapSet `seed/2` arg, fuel-test construction, `declare/3` list arg, ctor `result_params`) | `35c320d` |
| 4 — Execute (Opus, TDD, one build at a time) | red → green per task, ghost-authored | `8cdedfb`, `f95efe7`, `64080da`, `a578ed0` |
| 5 — Verify | full suite; **found + fixed a pre-existing regression** (see below) | `2f7796a` |

### Per-task execution (Stage 4)

1. **`8cdedfb`** — assay clause + `run/2` seam + infer→Conv decision procedure + hole-skip + reject/crash handling. Red: no `elab/soundness` clause. Green 6/6.
2. **`f95efe7`** — constructor `check`-fallback. Red: sound parameter-bearing ctor misreported `{:core_ill_typed, :ok_mk, {:ctor_requires_checking_mode, :F}}`. Green 8/8.
3. **`64080da`** — fuel-bound per-def checks. Red: non-normalizing `loop`/`probe` timed out at 30s. Green 9/9 (fuel test returns in 0.1s).
4. **`a578ed0`** — `soundness_challenges/0` generator + runner dispatch. Red: undefined. Green 12/12 — whole catalog re-checks clean.

## Regression found + fixed during Stage 5 (not V3)

The first full-suite run failed one test: `CorpusReplayTest` "every committed entry
satisfies its assay invariant" — 87 seed entries replayed as
`{:unknown_assay, "kernel/*"}`. **Root cause:** the earlier seed-expansion commit
`b394149` (this session's fuel-calibration work) banked
`kernel/{shift_subst,weakening,confluence}` seeds, but the regression guard's
`@registry` fixture omitted the kernel-law (and elab) assay ids. That commit was
made without re-running this guard. **Fix** (`2f7796a`): complete `@registry` to
mirror `runner.ex`'s `assay_module/1` roster (added kernel/* + elab/*). Behavioral
assertion unchanged; the 87 seeds now dispatch to `KernelLaw` and satisfy their
invariant. Re-run: green.

## Verification

- **Full suite (single authorized run, then one re-run after the fix):** `2652
  passed` (3 doctests, 2649 tests), 0 failures — up +12 from the prior 2640 (the
  new `elab_soundness_test.exs` rows).
- **StreamData quarantine:** `architecture_test.exs` green (the assay adds no
  `StreamData` literal).
- **Campaign smoke:** `mix antigen --count 200` unchanged (0 infections — V3 runs
  via the catalog, not `default_gen`, by design).
- **Working tree:** clean (test-run seed/corpus side-effects reverted).
- Every commit ghost-authored (`Made In Heaven`), no `Co-Authored-By`.

## Boundaries (honest framing)

V3 **finds** unsound elaboration; it does not fix any (none surfaced). It re-checks
the emitted core of the curated completeness catalog — not a random surface-program
fuzzer (that would be a generator-expansion follow-on). `:elab_program` is a triage
no-op for term-shrink (Run D), unchanged. The kernel is the oracle, never modified.

## Next phases (umbrella roadmap, task #66)

- **Phase 2 — V1 normalizer** (`Core.Normalise` deepened + `Types.Reduce`
  differential, **plus** the intrinsic-law-only assay over the untranslatable
  fragment, per the operator's resolution).
- **Phase 3 — V2 unifier** covering **both** `Elab.Unify` and `Types.Unify`.
- Then V5 totality-closure, V4 erasure/relevance, V6 SMT lint.

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
