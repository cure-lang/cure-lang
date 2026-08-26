# Antigen kernel-law assays — Completion Report (Run B)

**Branch:** `autopilot/antigen-tier-b` · **Date:** 2026-07-03 · **Mode:** autopilot (design-approved gate → hands-off)

Three relational kernel-law assays added to Antigen, exercising the `Cure.Core.*`
de Bruijn substitution algebra, weakening, and reduction order-independence —
pure-Antigen, kernel public-API only, **no TCB edits**.

## What shipped

| Assay-id | Law tested | Shape |
|---|---|---|
| `kernel/shift_subst` | de Bruijn σ-algebra — 4 laws: identity `shift(t,0,0)=t`; composition `shift∘shift = shift(·,a+b)`; shift/subst commutation (`c≤j`); subst-of-fresh no-op | pure (no ctx) |
| `kernel/weakening` | infer → extend ctx with unused binder → `shift(t,1,0)` → re-infer → quoted types agree under shift; ill-typed ⇒ vacuous `:ok` | relational, kernel-driven |
| `kernel/confluence` | `nf(t)` == `whnf(t) → nf`; fuel-exhaustion on either path ⇒ vacuous `:ok` | relational, kernel-driven |

All three reuse the existing `:typed_term` challenge kind; each is dispatched by
assay-id in the new `Antigen.Assays.KernelLaw` module.

## Stage-by-stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Brainstorm + spec | design approved; spec written + self-reviewed | `14aa257`, `c9d969b` |
| 1 — Spec review (Sonnet subagent) | Tier-1 framing, full σ-laws, correctness ladder; converged | `6c48b61` |
| 2 — Plan | 3-task TDD plan | `5bd45a2` |
| 3 — Plan review (Sonnet subagent) | 4 passes, 5 doc issues fixed, all APIs trial-verified (suite run 2×), 0 impl changes | `25546c3` |
| 4 — Execute (Opus, TDD, one build at a time) | red → green per task, ghost-authored | `a3a83a7`, `826d095`, `468a173` |

### Per-task execution (Stage 4)

1. **`a3a83a7`** — widen `Term.typed_term/1` guard (`in @assay_ids` → `is_binary/1`) + 3 registry rows routing `kernel/*` → `KernelLaw`. Red: `FunctionClauseError` on both guard and registry. Green: 2/2.
2. **`826d095`** — `Antigen.Assays.KernelLaw` (`run/1` dispatching to `shift_subst`/`weakening`/`confluence`). Red: `UndefinedFunctionError`. Green: 8/8 — incl. the non-tautology re-derivation of laws 2 & 3 and the fuel-exhausting `plus(deep_s(700), Z)` vacuous fixture.
3. **`468a173`** — `default_gen` 11 → 14 branches + `@group_table` T-list → `[4,5,6,9,10,11,12,13,14]` + guard test updated. Red: guard test `11 ≠ 14`; integration test already green. Green: 10/10.

## Verification

- **Full suite (single authorized run):** `2577 passed` (3 doctests, 2574 tests), 0 failures.
- **Smoke run:** `mix antigen --count 800` → **0 infections**, 89 seeds banked; all verticals healthy (typed_term binder_usage 0.94 / reduction_activity 0.54; mutant survivors 0; conversion both-polarities 57 reject / 154 accept).
- **StreamData quarantine:** clean — no literal under `lib/antigen/generators/` or `lib/antigen/assays/`.
- **Working tree:** clean (test-run seed side-effect reverted).

## Boundaries (honest framing)

This is **testing, not proof.** The kernel-law assays are **Tier-1 extrinsic
property tests** on the de Bruijn σ-algebra — the correctness ladder's mechanized
/ intrinsic rungs (Idris differential oracle, Cure-model, self-hosted proof)
remain deferred per the spec. A green run is evidence the laws held over the
generated corpus, not a certificate that they hold universally.

## Next

- **Run C** (task #64): assay sensitivity meta-testing (simulated kernel weakenings).
- **Run D** (task #65): triage infrastructure (shrink-all-kinds + auto-bisect).

**Do NOT auto-merge.** Operator merges `autopilot/antigen-tier-b` on return.
