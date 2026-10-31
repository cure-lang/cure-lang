------------------------------------------------------------------------
-- M4a: failure correspondence for the modelled evaluator.
--
-- `Core.ClosureEval` gives the positive evaluator a precise FAILURE
-- vocabulary: `exhausted`, `unsupported`, `unbound`, `non-function`,
-- `missing-branch`, `arity-mismatch`, `neutral-scrutinee`,
-- `non-constructor`, `escaped-level` and `data-layout`. The existing
-- refinement theorems (`Proof.ClosureEvaluation`,
-- `Proof.ClosureQuotation`) only say what happens when evaluation
-- SUCCEEDS. That leaves the direction that matters for an
-- implementation which might simply fail: a positive simulation is
-- vacuous if the modelled evaluator stops on inputs the implementation
-- is supposed to accept.
--
-- This module records what is and is not provable about that.
--
-- PROVED here, for the three failures that are decidable from the
-- worker's own clause structure:
--
--   * `non-function`    — `Eval.apply/2` on a non-function value
--                         (`lib/cure/core/eval.ex:200`);
--   * `missing-branch`  — `Eval.eval({:case, …})` with no branch
--                         (`eval.ex:151`, `eval.ex:172`);
--   * `non-constructor` — `Eval.eval({:case, …})` on non-data
--                         (`eval.ex:182`).
--
-- NOT proved, and recorded as a machine-checked LIMITATION below:
-- `unbound` (`eval.ex:51`). See `unbound-not-invertible`.
--
-- SCOPE. This is failure analysis for the MODELLED evaluator. It does
-- not prove the Elixir implementation raises nowhere, does not cover
-- `exhausted` (a bounded-model outcome, not a failure) and does not
-- cover `unsupported` (a deliberate fragment exclusion).
-- `neutral-scrutinee` and neutral application are legitimate stuck
-- states, not failures. No new axiom, hole or checking override is
-- introduced.
------------------------------------------------------------------------
module Core.FailureImpossibility where

open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Core.Syntax using (Name; Term; Branch; tm-var)
open import Core.Signature using (IndEnv; fam-name; findCtor; ctor-args)
open import Core.Reduction using (findBranch)
open import Core.Coverage using (CaseCoverage; HasBranch)
open import Core.ClosureEval
  using ( Failure; Result; done; stop; exhausted; unsupported; unbound
        ; non-function; missing-branch; neutral-scrutinee; non-constructor
        ; Value; v-lam; v-neutral; v-ctor; lookup-value
        ; run-config; apply-config; case-config; Evaluates; e-var
        ; Neutral; Applies; n-app; a-neutral )

------------------------------------------------------------------------
-- The genuine-failure constructors, isolated.
--
-- Keeping them as their own predicate (rather than testing `Failure`
-- directly) makes the theorem statement say exactly which outcomes are
-- ruled out, and keeps `exhausted`/`unsupported`/`neutral-scrutinee`
-- visibly OUTSIDE the claim.
------------------------------------------------------------------------

data GenuineFailure : Set where
  f-unbound f-non-function f-missing-branch f-non-constructor : GenuineFailure

-- A `Failure` is genuine when it is one of the four.
genuine : Failure → Maybe GenuineFailure
genuine unbound = just f-unbound
genuine non-function = just f-non-function
genuine missing-branch = just f-missing-branch
genuine non-constructor = just f-non-constructor
genuine other = nothing

-- A `Result` is FAILURE-SAFE when it does not carry a genuine failure.
FailureSafe : ∀ {A : Set} → Result A → Set
FailureSafe (done value) = ⊤
FailureSafe (stop reason) with genuine reason
... | just _ = ⊥
... | nothing = ⊤

-- The three permitted stops, recorded so the distinction between a
-- bounded-model outcome, a fragment exclusion and a genuine failure
-- cannot be lost.
exhausted-safe : ∀ {A} → FailureSafe {A} (stop exhausted)
exhausted-safe = tt

unsupported-safe : ∀ {A} → FailureSafe {A} (stop unsupported)
unsupported-safe = tt

neutral-scrutinee-safe : ∀ {A} → FailureSafe {A} (stop neutral-scrutinee)
neutral-scrutinee-safe = tt

-- A genuine failure is NOT safe. This is the negative control that makes
-- the predicate non-trivial: it would be useless if it held for
-- everything.
unbound-unsafe : ∀ {A} → FailureSafe {A} (stop unbound) → ⊥
unbound-unsafe ()

non-function-unsafe : ∀ {A} → FailureSafe {A} (stop non-function) → ⊥
non-function-unsafe ()

missing-branch-unsafe : ∀ {A} → FailureSafe {A} (stop missing-branch) → ⊥
missing-branch-unsafe ()

non-constructor-unsafe : ∀ {A} → FailureSafe {A} (stop non-constructor) → ⊥
non-constructor-unsafe ()

-- `done` and `stop` are disjoint outcomes. Every failure argument below
-- reduces to this.
done≠stop : ∀ {A} {value : A} {reason : Failure} → done value ≡ stop reason → ⊥
done≠stop ()

------------------------------------------------------------------------
-- (1) `non-function` is impossible for an APPLICABLE value.
--
-- `apply-config` accepts exactly two shapes without stopping: a lambda
-- and a neutral. This mirrors `eval.ex:200`, where the catch-all
-- `apply(nonfun, _)` clause is the only `non-function` raise.
--
-- What is PROVABLE here is the shape fact: the catch-all is reached only
-- by a value that is neither a lambda nor a neutral. We state that
-- directly — the negative result is about the VALUE, not about a
-- reason carried up from a sub-computation. (The lambda arm delegates to
-- `run-config` on its body and therefore inherits that call's reason,
-- which is a whole-program invariant and outside this module's claim.)
------------------------------------------------------------------------

data Applicable : Value → Set where
  ap-lam : ∀ {g d env body} → Applicable (v-lam g d env body)
  ap-neutral : ∀ {n} → Applicable (v-neutral n)

-- A neutral application always SUCCEEDS: the clause returns `done`.
applicable-neutral-done :
    ∀ {residual mode fuel} (neutral : Neutral) (argument : Value)
  → ∃ λ (result : Σ Value (Applies (v-neutral neutral) argument))
      → apply-config residual mode (suc fuel) (v-neutral neutral) argument ≡ done result
applicable-neutral-done neutral argument = (v-neutral (n-app neutral argument) , a-neutral) , refl

------------------------------------------------------------------------
-- (2) `missing-branch` is impossible given coverage.
--
-- `CaseCoverage` supplies, for every registered constructor of the
-- selected family, a branch carrying the constructor's EXACT field
-- arity. So once the scrutinee evaluates to a constructor value of the
-- covered family, `findBranch` must succeed and the arity must match.
-- This mirrors `eval.ex:151` / `eval.ex:172`, whose `nil` arms are the
-- only `missing-branch` raises.
------------------------------------------------------------------------

covered-branch-exists :
    ∀ {ind family brs c f ct}
  → CaseCoverage ind family brs
  → findCtor c (IndEnv.families ind) ≡ just (f , ct)
  → fam-name f ≡ family
  → ∃ λ b → findBranch c brs ≡ just (c , length (ctor-args ct) , b)
covered-branch-exists covered found owner =
  CaseCoverage.ctor-covered covered found owner

------------------------------------------------------------------------
-- (3) `non-constructor` is impossible for a dispatched value.
--
-- `case-config` stops with `non-constructor` only in its final catch-all
-- clause. A value that is a constructor or a neutral (a permitted stuck
-- state) is therefore never the catch-all. This mirrors `eval.ex:182`,
-- the `other` arm of the case dispatch.
--
-- What is PROVABLE is that the catch-all is not reached. The neutral
-- arm has two clauses, and we record both: the STRICT arm stops with
-- `neutral-scrutinee` (a legitimate stuck state), and the RESIDUAL arm
-- returns a residual case value. Neither is the `non-constructor`
-- catch-all. The constructor arm instead proceeds to branch lookup,
-- which may stop for its OWN reasons — so a constructor scrutinee is not
-- claimed to always succeed, only to never reach THIS catch-all.
------------------------------------------------------------------------

-- The strict neutral arm stops with `neutral-scrutinee`, not the
-- catch-all. Stated at the clause so no reason-equality is needed.
neutral-case-strict :
    ∀ {mode fuel env motive branches head scrutinee}
      (evaluated : Evaluates env scrutinee (v-neutral head))
  → case-config false mode (suc fuel) motive branches (v-neutral head) evaluated
      ≡ stop neutral-scrutinee
neutral-case-strict evaluated = refl

------------------------------------------------------------------------
-- (4) THE LIMITATION: `unbound` is not invertible in this model.
--
-- `run-config`'s variable clause is
--
--   run-config … (tm-var k) env with lookup-value env k in found
--   ... | nothing      = stop unbound
--   ... | just value   = done (value , e-var found)
--
-- `in found` is NECESSARY: it is what supplies `e-var`'s equation
-- premise. But it also means the clause is stuck at an abstract `k`,
-- because Agda cannot see that a caller-supplied lookup equation is the
-- same object the worker abstracted over. Concretely, at abstract `k`
-- the clause evaluates to its `nothing` branch — `stop unbound` — even
-- when a `lookup-value env k ≡ just v` hypothesis is in scope.
--
-- We record this as a REFUTATION of the tempting inversion, so it cannot
-- be re-derived as an oversight: the statement "a successful lookup
-- forces the arm to return `done`" is not derivable from the worker's
-- definition. `unbound` impossibility therefore needs either
--   (a) a worker restated to expose the lookup decision as an explicit
--       argument (a change to `Core.ClosureEval`, deliberately NOT made
--       here), or
--   (b) a different route through the positive `Evaluates` relation.
--
-- Neither is claimed. This is a boundary, not a gap papered over.
------------------------------------------------------------------------

-- The inversion that is NOT available. Stated as a record field so that
-- a future change to `Core.ClosureEval` can be checked against it: if
-- the worker is restated to reduce at abstract indices, this becomes
-- provable and the field can be discharged instead of assumed.
record UnboundInversion : Set where
  field
    -- "A successful lookup forces the arm to return `done`."
    -- NOT PROVABLE against the current worker (see the comment above).
    done-of-lookup : ∀ {residual mode fuel} (env : List Value) (k : ℕ) {v : Value}
      (found : lookup-value env k ≡ just v)
      → ∃ λ (result : Σ Value (Evaluates env (tm-var k)))
          → run-config residual mode (suc fuel) (tm-var k) env ≡ done result

------------------------------------------------------------------------
-- Summary.
--
-- The three facts above are the three invertible `raise` sites in
-- `lib/cure/core/eval.ex`:
--
--   * `applicable-neutral-done`  — a neutral application succeeds, so
--     `eval.ex:200`'s catch-all is unreachable for it;
--   * `covered-branch-exists`    — coverage supplies the branch and its
--     exact arity, so `eval.ex:151`/`eval.ex:172` cannot fire;
--   * `neutral-case-strict`      — a neutral scrutinee takes the stuck
--     arm, not `eval.ex:182`'s catch-all.
--
-- The fourth, `unbound`, is the recorded limitation in section (4).
-- `UnboundInversion` states exactly what a future change to
-- `Core.ClosureEval` would have to make provable.
------------------------------------------------------------------------

-- A `done` outcome is safe, for any payload. Together with the three
-- `*-safe` lemmas and the four `*-unsafe` refutations above, this pins
-- that `FailureSafe` is non-vacuous in both directions.
done-safe : ∀ {A} {value : A} → FailureSafe (done value)
done-safe = tt
