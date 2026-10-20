------------------------------------------------------------------------
-- Full recursive preservation on real compact literals. Only source
-- typings are assembled; every target below comes from Subject.Preserve.
-- Field-sensitive cases distinguish the bound from the predecessor.
------------------------------------------------------------------------
module Proof.DependentSubjectReductionLiterals where

open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Signature
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Typing using (⟨⟩; Ctx; extend; Conversion)
open import Core.Reduction
open import Core.Coverage
import Core.DependentTyping as Native
open import Proof.Progress
  using (Final; FinalBranches; f-case; f-lam; f-data; f-nat_lit;
    f-bounded_lit; f-float_type; f-float_lit; f-var; ft[]; fb[]; fb∷)
import Proof.DependentLiteralExamples as E
import Proof.DependentSubjectReduction as Subject
open E.T
module P = Subject.Preserve E.env E.sig E.conv E.valid E.D.data-components
  E.R.reduce-converts (λ ()) E.shapes

-- Every root exercises all three public preservation entry points at
-- exactly the source's original goal, without a target typing premise.
all-routes : ∀ {t u goal}
  → ⟨⟩ ⊢ t ⇒ goal → Final t → _⇝_ E.sig t u
  → (⟨⟩ ⊢ u ⇐ goal) × (⟨⟩ ⊢ u ⇐ goal) × (⟨⟩ ⊢ u ⇒ goal)
all-routes source final step =
  P.preservation⇒ wf[] source final step ,
  P.preservation⇐ wf[] (E.check source) final step ,
  P.preservation-infers wf[] source final step

nat-source : ∀ k → ⟨⟩ ⊢ tm-case (tm-nat_lit k) E.nat-motive E.nat-branches
  ⇒ Native.apps E.nat-motive (tm-nat_lit k ∷ [])
nat-source k = ⇒-case wf[] refl (E.nat-chain k) sp[] sp[]
  E.nat-motive-valid E.nat-branches-valid E.nat-coverage
bounded-source : ∀ k → ⟨⟩ ⊢ tm-case (tm-bounded_lit k) E.bounded-motive E.bounded-branches
  ⇒ Native.apps E.bounded-motive (tm-bounded_lit k ∷ [])
bounded-source k = ⇒-case wf[] refl (E.bounded-chain k) sp[] sp[]
  E.bounded-motive-valid E.bounded-branches-valid E.bounded-coverage
nat-final : ∀ k → Final (tm-case (tm-nat_lit k) E.nat-motive E.nat-branches)
nat-final k = f-case f-nat_lit (f-lam (f-data ft[] ft[]) f-float_type)
  (fb∷ f-float_lit (fb∷ f-float_lit fb[]))
bounded-final : ∀ k → Final (tm-case (tm-bounded_lit k) E.bounded-motive E.bounded-branches)
bounded-final k = f-case f-bounded_lit (f-lam (f-data ft[] ft[]) f-float_type)
  (fb∷ f-float_lit (fb∷ f-float_lit fb[]))

nat-zero-step : _⇝_ E.sig (tm-case (tm-nat_lit 0) E.nat-motive E.nat-branches) tm-float_lit
nat-zero-step = ι-nat-zero refl refl
nat-suc-step : _⇝_ E.sig (tm-case (tm-nat_lit 8) E.nat-motive E.nat-branches) tm-float_lit
nat-suc-step = ι-nat-suc refl refl
bounded-zero-step : _⇝_ E.sig (tm-case (tm-bounded_lit 0) E.bounded-motive E.bounded-branches) tm-float_lit
bounded-zero-step = ι-bounded-zero refl refl
bounded-suc-step : _⇝_ E.sig (tm-case (tm-bounded_lit 8) E.bounded-motive E.bounded-branches) tm-float_lit
bounded-suc-step = ι-bounded-suc refl refl

nat-zero-results :
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.nat-motive (tm-nat_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.nat-motive (tm-nat_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇒ Native.apps E.nat-motive (tm-nat_lit 0 ∷ []))
nat-zero-results = all-routes (nat-source 0) (nat-final 0) nat-zero-step
nat-suc-results :
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.nat-motive (tm-nat_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.nat-motive (tm-nat_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇒ Native.apps E.nat-motive (tm-nat_lit 8 ∷ []))
nat-suc-results = all-routes (nat-source 8) (nat-final 8) nat-suc-step
bounded-zero-results :
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.bounded-motive (tm-bounded_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.bounded-motive (tm-bounded_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇒ Native.apps E.bounded-motive (tm-bounded_lit 0 ∷ []))
bounded-zero-results = all-routes (bounded-source 0) (bounded-final 0) bounded-zero-step
bounded-suc-results :
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.bounded-motive (tm-bounded_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇐ Native.apps E.bounded-motive (tm-bounded_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-float_lit ⇒ Native.apps E.bounded-motive (tm-bounded_lit 8 ∷ []))
bounded-suc-results = all-routes (bounded-source 8) (bounded-final 8) bounded-suc-step

-- General coverage for the same declarations but arbitrary source bodies.
nat-coverage : ∀ z s → CaseCoverage E.env "LiteralNat" (("Z" , 0 , z) ∷ ("S" , 1 , s) ∷ [])
nat-coverage z s = record
  { ctor-covered = λ {name} → covered {name}
  ; nat-zero-covered = λ identity → z , refl
  ; nat-suc-covered = λ identity → s , refl
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }
  where
    covered : ∀ {name f ct}
      → findCtor name (IndEnv.families E.env) ≡ just (f , ct) → fam-name f ≡ "LiteralNat"
      → HasBranch name (length (ctor-args ct)) (("Z" , 0 , z) ∷ ("S" , 1 , s) ∷ [])
    covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families E.env} found
    ... | here refl , here refl , refl = z , refl
    ... | here refl , there (here refl) , refl = s , refl
    ... | here refl , there (there ()) , equal
    covered found () | there (here refl) , member , equal
    covered found owner | there (there ()) , member , equal
bounded-coverage : ∀ first next → CaseCoverage E.env "LiteralBounded"
  (("First" , 1 , first) ∷ ("Next" , 2 , next) ∷ [])
bounded-coverage first next = record
  { ctor-covered = λ {name} → covered {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ identity → first , refl
  ; bounded-suc-covered = λ identity → next , refl }
  where
    covered : ∀ {name f ct}
      → findCtor name (IndEnv.families E.env) ≡ just (f , ct) → fam-name f ≡ "LiteralBounded"
      → HasBranch name (length (ctor-args ct)) (("First" , 1 , first) ∷ ("Next" , 2 , next) ∷ [])
    covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families E.env} found
    covered found () | here refl , member , equal
    ... | there (here refl) , here refl , refl = first , refl
    ... | there (here refl) , there (here refl) , refl = next , refl
    ... | there (here refl) , there (there ()) , equal
    ... | there (there ()) , member , equal

nat-at-goal : ∀ {n} {Γ : Ctx n} {t domain arg} → Γ ⊢ t ⇒ E.nat-goal
  → Γ ⊢ t ⇐ tm-app (tm-lam unrestricted domain E.nat-goal) arg
nat-at-goal {domain = domain} {arg} source = ⇐-infer source
  (Conversion.≈-sym E.conv
    {t = tm-app (tm-lam unrestricted domain E.nat-goal) arg} {u = E.nat-goal}
    (E.R.reduce-converts {t = tm-app (tm-lam unrestricted domain E.nat-goal) arg}
      {u = E.nat-goal} β))
bounded-at-goal : ∀ {n} {Γ : Ctx n} {t domain arg} → Γ ⊢ t ⇒ E.bounded-goal
  → Γ ⊢ t ⇐ tm-app (tm-lam unrestricted domain E.bounded-goal) arg
bounded-at-goal {domain = domain} {arg} source = ⇐-infer source
  (Conversion.≈-sym E.conv
    {t = tm-app (tm-lam unrestricted domain E.bounded-goal) arg} {u = E.bounded-goal}
    (E.R.reduce-converts {t = tm-app (tm-lam unrestricted domain E.bounded-goal) arg}
      {u = E.bounded-goal} β))

nat-predecessor-motive bounded-predecessor-motive bounded-bound-motive : Term
nat-predecessor-motive = tm-lam unrestricted E.nat-goal E.nat-goal
bounded-predecessor-motive = tm-lam unrestricted E.bounded-goal E.bounded-goal
bounded-bound-motive = tm-lam unrestricted E.bounded-goal E.nat-goal
nat-predecessor-motive-valid : Motive ⟨⟩ E.nat [] nat-predecessor-motive l0
nat-predecessor-motive-valid = motive (sc-lam E.nat-scoped E.nat-scoped)
  (⇒-pi E.nat-kind (⇒-type refl)) (⇒-lam E.nat-kind (E.check E.nat-kind))
bounded-predecessor-motive-valid : Motive ⟨⟩ E.bounded [] bounded-predecessor-motive l0
bounded-predecessor-motive-valid = motive (sc-lam E.bounded-scoped E.bounded-scoped)
  (⇒-pi E.bounded-kind (⇒-type refl)) (⇒-lam E.bounded-kind (E.check E.bounded-kind))
bounded-bound-motive-valid : Motive ⟨⟩ E.bounded [] bounded-bound-motive l0
bounded-bound-motive-valid = motive (sc-lam E.bounded-scoped E.nat-scoped)
  (⇒-pi E.bounded-kind (⇒-type refl)) (⇒-lam E.bounded-kind (E.check E.nat-kind))

nat-fields bounded-fields bound-fields : List Branch
nat-fields = ("Z" , 0 , tm-nat_lit 0) ∷ ("S" , 1 , tm-var 0) ∷ []
bounded-fields = ("First" , 1 , tm-bounded_lit 0) ∷ ("Next" , 2 , tm-var 0) ∷ []
bound-fields = ("First" , 1 , tm-var 0) ∷ ("Next" , 2 , tm-var 1) ∷ []
nat-fields-valid : Branches ⟨⟩ E.nat [] nat-predecessor-motive nat-fields
nat-fields-valid = br∷ refl refl Native.op[] wf[]
  (nat-at-goal (⇒-nat_lit refl refl refl refl))
  (br∷ refl refl (Native.op∷ Native.op[]) (wf∷ wf[] E.nat-scoped E.nat-kind)
    (nat-at-goal (⇒-var Fin.zero)) br[])
bounded-fields-valid : Branches ⟨⟩ E.bounded [] bounded-predecessor-motive bounded-fields
bounded-fields-valid = br∷ refl refl (Native.op∷ Native.op[])
  (wf∷ wf[] E.nat-scoped E.nat-kind)
  (bounded-at-goal (⇒-bounded_lit refl refl refl refl))
  (br∷ refl refl (Native.op∷ (Native.op∷ Native.op[]))
    (wf∷ (wf∷ wf[] E.nat-scoped E.nat-kind) E.bounded-scoped E.bounded-kind)
    (bounded-at-goal (⇒-var Fin.zero)) br[])
bound-fields-valid : Branches ⟨⟩ E.bounded [] bounded-bound-motive bound-fields
bound-fields-valid = br∷ refl refl (Native.op∷ Native.op[])
  (wf∷ wf[] E.nat-scoped E.nat-kind) (nat-at-goal (⇒-var Fin.zero))
  (br∷ refl refl (Native.op∷ (Native.op∷ Native.op[]))
    (wf∷ (wf∷ wf[] E.nat-scoped E.nat-kind) E.bounded-scoped E.bounded-kind)
    (nat-at-goal (⇒-var (Fin.suc Fin.zero))) br[])

nat-field-source : ∀ k → ⟨⟩ ⊢ tm-case (tm-nat_lit k) nat-predecessor-motive nat-fields
  ⇒ Native.apps nat-predecessor-motive (tm-nat_lit k ∷ [])
nat-field-source k = ⇒-case wf[] refl (E.nat-chain k) sp[] sp[]
  nat-predecessor-motive-valid nat-fields-valid (nat-coverage (tm-nat_lit 0) (tm-var 0))
bounded-field-source : ∀ k → ⟨⟩ ⊢ tm-case (tm-bounded_lit k) bounded-predecessor-motive bounded-fields
  ⇒ Native.apps bounded-predecessor-motive (tm-bounded_lit k ∷ [])
bounded-field-source k = ⇒-case wf[] refl (E.bounded-chain k) sp[] sp[]
  bounded-predecessor-motive-valid bounded-fields-valid
  (bounded-coverage (tm-bounded_lit 0) (tm-var 0))
bound-field-source : ∀ k → ⟨⟩ ⊢ tm-case (tm-bounded_lit k) bounded-bound-motive bound-fields
  ⇒ Native.apps bounded-bound-motive (tm-bounded_lit k ∷ [])
bound-field-source k = ⇒-case wf[] refl (E.bounded-chain k) sp[] sp[]
  bounded-bound-motive-valid bound-fields-valid (bounded-coverage (tm-var 0) (tm-var 1))

nat-field-final : ∀ k → Final (tm-case (tm-nat_lit k) nat-predecessor-motive nat-fields)
nat-field-final k = f-case f-nat_lit (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
  (fb∷ f-nat_lit (fb∷ f-var fb[]))
bounded-field-final : ∀ k → Final (tm-case (tm-bounded_lit k) bounded-predecessor-motive bounded-fields)
bounded-field-final k = f-case f-bounded_lit (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
  (fb∷ f-bounded_lit (fb∷ f-var fb[]))
bound-field-final : ∀ k → Final (tm-case (tm-bounded_lit k) bounded-bound-motive bound-fields)
bound-field-final k = f-case f-bounded_lit (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
  (fb∷ f-var (fb∷ f-var fb[]))

nat-predecessor-step : _⇝_ E.sig (tm-case (tm-nat_lit 8) nat-predecessor-motive nat-fields) (tm-nat_lit 7)
nat-predecessor-step = ι-nat-suc refl refl
bounded-predecessor-step : _⇝_ E.sig
  (tm-case (tm-bounded_lit 8) bounded-predecessor-motive bounded-fields) (tm-bounded_lit 7)
bounded-predecessor-step = ι-bounded-suc refl refl
bounded-bound-step : _⇝_ E.sig
  (tm-case (tm-bounded_lit 8) bounded-bound-motive bound-fields) (tm-nat_lit 7)
bounded-bound-step = ι-bounded-suc refl refl

nat-predecessor-results :
  (⟨⟩ ⊢ tm-nat_lit 7 ⇐ Native.apps nat-predecessor-motive (tm-nat_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 7 ⇐ Native.apps nat-predecessor-motive (tm-nat_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 7 ⇒ Native.apps nat-predecessor-motive (tm-nat_lit 8 ∷ []))
nat-predecessor-results = all-routes (nat-field-source 8) (nat-field-final 8) nat-predecessor-step
bounded-predecessor-results :
  (⟨⟩ ⊢ tm-bounded_lit 7 ⇐ Native.apps bounded-predecessor-motive (tm-bounded_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-bounded_lit 7 ⇐ Native.apps bounded-predecessor-motive (tm-bounded_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-bounded_lit 7 ⇒ Native.apps bounded-predecessor-motive (tm-bounded_lit 8 ∷ []))
bounded-predecessor-results = all-routes (bounded-field-source 8) (bounded-field-final 8) bounded-predecessor-step
bounded-bound-results :
  (⟨⟩ ⊢ tm-nat_lit 7 ⇐ Native.apps bounded-bound-motive (tm-bounded_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 7 ⇐ Native.apps bounded-bound-motive (tm-bounded_lit 8 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 7 ⇒ Native.apps bounded-bound-motive (tm-bounded_lit 8 ∷ []))
bounded-bound-results = all-routes (bound-field-source 8) (bound-field-final 8) bounded-bound-step

nat-fallback-step : _⇝_ E.sig
  (tm-case (tm-nat_lit 0) nat-predecessor-motive nat-fields) (tm-nat_lit 0)
nat-fallback-step = ι-nat-zero refl refl
bounded-fallback-step : _⇝_ E.sig
  (tm-case (tm-bounded_lit 0) bounded-predecessor-motive bounded-fields) (tm-bounded_lit 0)
bounded-fallback-step = ι-bounded-zero refl refl
bound-first-step : _⇝_ E.sig
  (tm-case (tm-bounded_lit 0) bounded-bound-motive bound-fields) (tm-nat_lit 0)
bound-first-step = ι-bounded-zero refl refl

nat-fallback-results :
  (⟨⟩ ⊢ tm-nat_lit 0 ⇐ Native.apps nat-predecessor-motive (tm-nat_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 0 ⇐ Native.apps nat-predecessor-motive (tm-nat_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 0 ⇒ Native.apps nat-predecessor-motive (tm-nat_lit 0 ∷ []))
nat-fallback-results = all-routes (nat-field-source 0) (nat-field-final 0) nat-fallback-step
bounded-fallback-results :
  (⟨⟩ ⊢ tm-bounded_lit 0 ⇐ Native.apps bounded-predecessor-motive (tm-bounded_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-bounded_lit 0 ⇐ Native.apps bounded-predecessor-motive (tm-bounded_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-bounded_lit 0 ⇒ Native.apps bounded-predecessor-motive (tm-bounded_lit 0 ∷ []))
bounded-fallback-results = all-routes (bounded-field-source 0) (bounded-field-final 0) bounded-fallback-step
bound-first-results :
  (⟨⟩ ⊢ tm-nat_lit 0 ⇐ Native.apps bounded-bound-motive (tm-bounded_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 0 ⇐ Native.apps bounded-bound-motive (tm-bounded_lit 0 ∷ [])) ×
  (⟨⟩ ⊢ tm-nat_lit 0 ⇒ Native.apps bounded-bound-motive (tm-bounded_lit 0 ∷ []))
bound-first-results = all-routes (bound-field-source 0) (bound-field-final 0) bound-first-step
