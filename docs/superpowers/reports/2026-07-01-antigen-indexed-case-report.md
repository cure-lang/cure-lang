# Antigen indexed-family `case` vertical — completion report

**Branch:** `autopilot/cure-dependent-types-frp` (NOT merged — operator merges)
**Date:** 2026-07-01
**Final full suite:** 2132 passed, 0 failures (3 doctests, 2129 tests)

## What this run did

Added a fifth Antigen "deep-cut" soundness vertical — dependent-`case` typing —
on top of the merged surface-equality-proof kernel. Four obligations, each built
and run one at a time (spec §4). Found and fixed one soundness hole, documented
one incompleteness, and banked a permanent regression antibody.

## Stage outcomes

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 Brainstorm | GADT indexed-case vertical selected (prior session) | `be529dd` spec |
| 1 Spec review | hardened (removed a false "impossible-branch" hypothesis; fixed the 4.3 construction) | `be529dd` |
| 2 Plan | 6 tasks, payload `%{families, def_name, def_type, def_body}` | `94b4e33` |
| 3 Plan review | hardened (4.3 unsound-as-a-test → external-hypothesis form; `r.entry.assay` fix) | `50699e6` |
| merge | pulled in Codex's surface `Eq`/`refl`/`rewrite` + normalization; resolved `normalize/2` conflict; fixed a latent atom-interning bug | `fdc30ab` |
| 4 Execute | 6 tasks, TDD, one build at a time | `7a513c1`,`ac16a9c`,`30e46c6`,`504c474`,`27a5475`,`060930b` |
| 5 Verify | full suite green; this report; push notification | — |

## Findings

### 4.1 branch-family discipline — SOUNDNESS HOLE, FIXED (`ac16a9c`)
The case-checker admitted a branch naming a constructor of a **foreign family**.
`check_case_branches` looked up the branch ctor in the *global* namespace and
`check_coverage` only enforced `declared ⊆ covered` (never rejecting extra
names), so a `Dec` case with an extra `MkFoo` (a `Foo` ctor) branch was accepted
— the constant motive `λx:Dec. Dec` applied to the `MkFoo` value still yields
`Dec`, and the body `Dcoupled : Dec` checks.
**Fix:** `check_case_branches` now takes the scrutinee family `dname` and rejects
any branch whose ctor belongs to another family (`{:error, {:foreign_ctor, _}}`),
before its body is checked. Red→green kernel test:
`test/cure/core/case_soundness_test.exs`. No regression in `case_typing_test.exs`.
**Antibody banked:** `test/antigen/corpus.sexp` (replays `:ok` post-fix; goes red
if the fix regresses).

### 4.2 coverage exactness — SOUND (no change)
`check_coverage` already rejects a non-exhaustive case (`{:error, :coverage}`).

### 4.3 compound-index refinement — INCOMPLETENESS, DOCUMENTED (not patched)
The crown-jewel probe. `branch_index_subst` records a refinement equation only
when a ctor's result index is a bare `{:var, i}`; a **ground/compound** result
index (here `wrap : (p:Dec) -> Ix(Causal)`) is silently dropped. So reusing a
hypothesis `h : Ix n` (bound before the case at the unrefined index) inside the
`wrap` branch, where the required type is `Ix Causal`, is **wrongly rejected**
(`{:violation, {:wrongly_rejected, {:refine, :branch_type}}}`) — `h`'s unrefined
`Ix n` fails conversion against `Ix Causal`.
This is *incompleteness*, not unsoundness (rejection, not acceptance), so per
spec §5/criterion 5 it is **reported, not fixed**. The obligation also carries a
separate wrong-body soundness probe (branch body `{:type,0}` where `Dec` is
expected) which the kernel correctly rejects.

### 4.4 motive well-formedness — SOUND (no change)
An over-applied motive (extra `:lam` layer) is rejected as `:bad_motive` by
`infer_type_value_sort`'s catch-all. (Used over-application, not under-
application, which would crash `Eval.apply`.)

## Operator decisions taken mid-run

- **`Ix` vs `Eq`/`refl` for 4.3:** kept `Ix` (unification-style context
  refinement — what Idris/Agda do natively). The `Eq`/`refl` first attempt was
  rejected in review for giving zero signal (motive reduces to `Eq Dec Causal
  Causal` regardless of the drop).
- **Case-refinement / `rewrite` duplication:** the case-checker's
  `specialize_branch_context` (syntactic, partial — drops ground indices) and
  Codex's `{:rewrite,…}` (`Eval.apply(motive, endpoint)` — semantic, total) are
  the same "push an index equation through a type" operation done two ways.
  **Decision: finish the audit first, then spec the unification as its own
  initiative** — keep the audit net in place and green before touching the TCB.
  See NEXT.

## NEXT (separately-specced initiatives, not in this run)

1. **Unify case-refinement with the `rewrite`/transport path.** Direction A:
   route `specialize_branch_context` through the same motive-transport machinery
   as `{:rewrite,…}` (generalizes to ground/compound indices for free, closing
   the 4.3 incompleteness). Direction B: elaborate `case` → eliminators and make
   `rewrite` the `Eq`-recursor (Lean/Coq-style). Needs its own soundness argument;
   validate against the now-green Antigen indexed-case suite.
2. **A meaningful `Eq`/`rewrite` obligation** exercising Codex's reworked
   `{:rewrite,…}` normalization (a *good* propositional-equality probe, unlike the
   rejected 4.3 first attempt).
3. **Targeted alternative to (1):** if unification is deferred, a smaller fix is
   generalizing `branch_index_subst` to record ground-index equations.

## To merge

`git merge autopilot/cure-dependent-types-frp` from the target branch after review.
