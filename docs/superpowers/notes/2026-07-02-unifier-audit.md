# Phase 1 — Unifier audit (`unify_indices` vs Lean `unifyEq?`)

**Date:** 2026-07-02. **Scope:** read-only audit (plan Phase 1). **Verdict: GAP — one structural, two completeness.**

## What was audited

`lib/cure/core/kernel.ex:787-885` (`unify_indices` + `unify_one`/`bind_index`/`reduce_index_pairs`/`unify_spine`), its two consumers (`check_case_branches` kernel.ex:720, `branch_unify` kernel.ex:770), against Lean `src/Lean/Meta/Tactic/UnifyEq.lean` (`unifyEq?`, :48-140) and `src/Lean/Meta/Tactic/Cases.lean` (`unifyEqs?`, :231-236) — read in source per the operator directive, and post-dating the Phase-4a conversion fix (09a80f3).

## Rule-by-rule status

| Rule | Lean (`unifyEq?`) | Cure (`unify_indices`) | Status |
|---|---|---|---|
| solution | `substCore` (:73), both orientations | both orientations (:811 ctor-var, :814 outer-var), disjoint de Bruijn ranges make direction unambiguous; same-key merge conflict detected (:853) | ✅ parity |
| injectivity | `injectionCore` (:108) | ctor/ctor (:817), data/data flattened spine (:822) | ✅ parity (flattened-spine caveat is the known Phase-5 reify collapse, reach-pinned) |
| conflict | `noConfusion` via injection `solved` (:109) | rigid head clash → `:impossible` (:828-833) | ✅ parity |
| cycle | `acyclic` closes the goal = impossible (:78) | occurs-check → `:undecided` (:848) | ⚠️ sound but INCOMPLETE — an impossible cyclic branch (`n = S n`) gets its body checked instead of skipped. Demand-driven; revisit only if Phase 6 hits it. |
| deletion | **`isDefEq`** (:75, :136) — definitional | syntactic `==` (:826) | ⚠️ INCOMPLETE — post-4a, `Conv.conv_values?` is strictly stronger (decides `plus(Z,y) ≐ y`). Faithful port = Conv-based deletion. Low-risk, but TCB; fold into the Phase 2 gate. |

## The structural gap (blocks Phase 2 as-is)

Lean's unifier operates **on a goal whose equations are hypotheses**: when no rule applies, the stuck equation *remains in the goal* — that IS the carried equality. Cure's `unify_indices` returns only `{:solved, subst} | :trivial | :impossible`, and `:undecided` pairs are **silently dropped** (`reduce_index_pairs` kernel.ex:805, `unify_spine` kernel.ex:840). Sound today (the branch is checked in a less-specialized context — conservative), but the stuck pairs are exactly the equations Phase 2 must inject as motive-carried `Eq` hypotheses. There is nothing for the front-end to carry.

**Minimal kernel change (Phase 2, gated — NOT implemented here):**

1. Thread a `residuals` accumulator of `:undecided` pairs `{r_term, s_term}` (both already in the branch de Bruijn frame after the `:793` shift) through `reduce_index_pairs`/`unify_spine`/`bind_index`'s `:undecided` outcomes.
2. Verdict grows to `{:solved, subst, residuals}` / `:trivial` (only when subst AND residuals empty) / `:impossible`; `branch_unify` re-exports it.
3. Deletion upgraded to `Conv.conv_values?` (per Lean :75) so definitionally-equal pairs are dropped rather than carried — keeps residuals minimal and leans on the 4a-fixed conversion.
4. Consumers: `check_case_branches` initially ignores residuals (behavior-preserving); Phase 2's motive rule types each residual as `Eq(IndexTy, r, s)`.

**Named red test (Phase 2, Task 2.x):** `test/cure/core/branch_unify_residual_test.exs` — `branch_unify` on an SF-shaped family whose ctor result index is a stuck application (`app(av, bv)` over telescope vars) against a scrutinee index that is a *different* stuck neutral: today both sides are non-rigid → `:undecided` → dropped → verdict `:trivial`; the red assertion demands the residual pair be exposed.

## Also confirmed in passing

- `unifyEq?`'s Nat-offset special case (:83-102, `Nat.elimOffset`) has no Cure analog; not needed for the FRP cluster.
- The occurs-check over-approximation (kernel.ex:879-885) can only produce spurious `:undecided`, never an unsound bind — consistent with "uncertainty is always `:undecided`, never `:impossible`" (kernel.ex:786).
