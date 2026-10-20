------------------------------------------------------------------------
-- Computational policy controls. A raw observation is a Value/step
-- witness, NOT a native type validator or a release-admission judgment.
------------------------------------------------------------------------
module Proof.DependentObservationExamples where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature using (IndEnv)
open import Core.Grade using (unrestricted)
open import Core.TypeHeads
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Reduction
import Core.DependentTyping as Native
open import Proof.Progress using (Final; f-app; f-lam; f-atom_type; f-var; f-float_lit)
import Proof.DependentTypingInversion as Inversion
import Proof.DependentObservation as Observation
import Proof.DependentProgressExamples as ProgressExamples

module Raw (sig : Signature) where
  open Observation.Policy sig

  -- A skipped unrelated branch and duplicate matching branches exercise
  -- actual first-match semantics, not propositional list membership.
  duplicate-branches : List Branch
  duplicate-branches =
    ("Other" , 0 , tm-float_lit) ∷
    ("K" , 0 , tm-atom_lit "first") ∷
    ("K" , 0 , tm-atom_lit "second") ∷ []
  duplicate-lookup :
    Observation.lookup-branch "K" duplicate-branches
      ≡ just (0 , tm-atom_lit "first" , refl)
  duplicate-lookup = refl
  duplicate-choice :
    candidate (tm-case (tm-ctor "K" []) tm-float_type duplicate-branches)
      ≡ just (inj₂ (tm-atom_lit "first" , ι refl refl))
  duplicate-choice = refl

  -- A malformed first matching branch MUST NOT be skipped to reach a
  -- later same-name branch with a convenient arity.
  wrong-first : List Branch
  wrong-first =
    ("K" , 1 , tm-var 0) ∷ ("K" , 0 , tm-atom_lit "second") ∷ []
  wrong-first-choice :
    candidate (tm-case (tm-ctor "K" []) tm-float_type wrong-first) ≡ nothing
  wrong-first-choice = refl
  missing-ordinary :
    candidate (tm-case (tm-ctor "Missing" []) tm-float_type duplicate-branches) ≡ nothing
  missing-ordinary = refl

  pair-fields : List Term
  pair-fields = tm-atom_lit "first" ∷ tm-float_lit ∷ []
  pair-branches : List Branch
  pair-branches = ("Pair" , 2 , tm-var 1) ∷ []
  ordinary-frame-order :
    candidate (tm-case (tm-ctor "Pair" pair-fields) tm-atom_type pair-branches)
      ≡ just (inj₂ (tm-atom_lit "first" , ι refl refl))
  ordinary-frame-order = refl
  ordinary-bad-arity :
    candidate (tm-case (tm-ctor "Pair" pair-fields) tm-atom_type
      (("Pair" , 1 , tm-var 0) ∷ [])) ≡ nothing
  ordinary-bad-arity = refl

  nat-branches bounded-branches bound-branches : List Branch
  nat-branches = ("Z" , 0 , tm-nat_lit 0) ∷ ("S" , 1 , tm-var 0) ∷ []
  bounded-branches =
    ("First" , 1 , tm-var 0) ∷ ("Next" , 2 , tm-var 0) ∷ []
  bound-branches =
    ("First" , 1 , tm-var 0) ∷ ("Next" , 2 , tm-var 1) ∷ []
  nat-zero-choice :
    candidate (tm-case (tm-nat_lit 0) tm-float_type nat-branches)
      ≡ just (inj₂ (tm-nat_lit 0 , ι-nat-zero refl refl))
  nat-zero-choice = refl
  nat-suc-choice :
    candidate (tm-case (tm-nat_lit 8) tm-float_type nat-branches)
      ≡ just (inj₂ (tm-nat_lit 7 , ι-nat-suc refl refl))
  nat-suc-choice = refl
  bounded-zero-choice :
    candidate (tm-case (tm-bounded_lit 0) tm-float_type bounded-branches)
      ≡ just (inj₂ (tm-nat_lit 0 , ι-bounded-zero refl refl))
  bounded-zero-choice = refl
  bounded-suc-predecessor :
    candidate (tm-case (tm-bounded_lit 8) tm-float_type bounded-branches)
      ≡ just (inj₂ (tm-bounded_lit 7 , ι-bounded-suc refl refl))
  bounded-suc-predecessor = refl
  bounded-suc-bound :
    candidate (tm-case (tm-bounded_lit 8) tm-float_type bound-branches)
      ≡ just (inj₂ (tm-nat_lit 7 , ι-bounded-suc refl refl))
  bounded-suc-bound = refl

  nat-zero-bad-arity :
    candidate (tm-case (tm-nat_lit 0) tm-float_type
      (("Z" , 1 , tm-var 0) ∷ [])) ≡ nothing
  nat-zero-bad-arity = refl
  nat-suc-bad-arity :
    candidate (tm-case (tm-nat_lit 8) tm-float_type
      (("S" , 0 , tm-float_lit) ∷ [])) ≡ nothing
  nat-suc-bad-arity = refl
  bounded-zero-bad-arity :
    candidate (tm-case (tm-bounded_lit 0) tm-float_type
      (("First" , 0 , tm-float_lit) ∷ [])) ≡ nothing
  bounded-zero-bad-arity = refl
  bounded-suc-bad-arity :
    candidate (tm-case (tm-bounded_lit 8) tm-float_type
      (("Next" , 1 , tm-var 0) ∷ [])) ≡ nothing
  bounded-suc-bad-arity = refl
  nat-zero-missing :
    candidate (tm-case (tm-nat_lit 0) tm-float_type []) ≡ nothing
  nat-zero-missing = refl
  nat-suc-missing :
    candidate (tm-case (tm-nat_lit 8) tm-float_type []) ≡ nothing
  nat-suc-missing = refl
  bounded-zero-missing :
    candidate (tm-case (tm-bounded_lit 0) tm-float_type []) ≡ nothing
  bounded-zero-missing = refl
  bounded-suc-missing :
    candidate (tm-case (tm-bounded_lit 8) tm-float_type []) ≡ nothing
  bounded-suc-missing = refl

  identity : Term
  identity = tm-lam unrestricted tm-atom_type (tm-var 0)
  beta-choice :
    candidate (tm-app identity (tm-atom_lit "payload"))
      ≡ just (inj₂ (tm-atom_lit "payload" , β))
  beta-choice = refl
  let-choice :
    candidate (tm-let unrestricted tm-atom_type (tm-atom_lit "payload") (tm-var 0))
      ≡ just (inj₂ (tm-atom_lit "payload" , ζ))
  let-choice = refl
  function-step-choice :
    candidate (tm-app
      (tm-let unrestricted tm-atom_type (tm-atom_lit "ignored") identity)
      (tm-atom_lit "payload"))
      ≡ just (inj₂ (tm-app identity (tm-atom_lit "payload") , ξ-app₁ ζ))
  function-step-choice = refl
  scrutinee-step-choice :
    candidate (tm-case
      (tm-let unrestricted tm-atom_type (tm-atom_lit "ignored") (tm-nat_lit 0))
      tm-float_type nat-branches)
      ≡ just (inj₂ (tm-case (tm-nat_lit 0) tm-float_type nat-branches , ξ-case ζ))
  scrutinee-step-choice = refl
  raw-hole-choice : ∀ name
    → candidate (tm-hole name) ≡ just (inj₁ (neutral n-hole))
  raw-hole-choice name = refl
  absurd-choice : candidate tm-absurd ≡ nothing
  absurd-choice = refl

-- This term has a genuine raw β witness even though its argument has
-- the wrong rigid type. Finality alone does not certify native typing.
bad-beta : Term
bad-beta = tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) tm-float_lit
bad-beta-final : Final bad-beta
bad-beta-final = f-app (f-lam f-atom_type f-var) f-float_lit

module NativeBoundary (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  module I = Inversion.Laws ind sig conv
  open Conversion conv
  module R = Observation.Policy sig

  raw-ill-typed-beta : R.candidate bad-beta ≡ just (inj₂ (tm-float_lit , β))
  raw-ill-typed-beta = refl
  raw-ill-typed-step : _⇝_ sig bad-beta tm-float_lit
  raw-ill-typed-step = β

  abstract
    float-atom-separate : tm-float_type ≈ tm-atom_type → ⊥
    float-atom-separate equal with
      ≈-heads {t = tm-float_type} {u = tm-atom_type} ty-float ty-atom equal
    ... | ()

    -- Native app inversion supplies the domain; native lambda inversion
    -- recovers Atom through every conversion intermediate. The literal's
    -- native principal type is Float, contradicting rigid-head equality.
    no-native-bad-beta : ∀ {A} → ⟨⟩ ⊢ bad-beta ⇒ A → ⊥
    no-native-bad-beta (⇒-app {g = g} {d = d} {c = c} function argument)
      with I.lambda-inference function
    ... | codomain , checked , equal = float-atom-separate
      (≈-trans {t = tm-float_type} {u = d} {v = tm-atom_type}
        (I.float-inference argument)
        (≈-sym {t = tm-atom_type} {u = d}
          (I.domain unrestricted tm-atom_type codomain g d c equal)))
    no-native-bad-beta (⇒-conv source eq) = no-native-bad-beta source
    no-native-bad-beta (⇒-cumul source le) = no-native-bad-beta source

    no-native-bad-beta-check : ∀ {A} → ⟨⟩ ⊢ bad-beta ⇐ A → ⊥
    no-native-bad-beta-check (⇐-infer source eq) = no-native-bad-beta source
    no-native-bad-beta-check (⇐-conv source eq) = no-native-bad-beta-check source
    no-native-bad-beta-check (⇐-cumul source le) = no-native-bad-beta source

  hole-not-final : ∀ {name} → Final (tm-hole name) → ⊥
  hole-not-final ()

module Globals where
  module G = ProgressExamples.Globals
  open Observation.Policy G.sig
  opaque-choice :
    candidate (tm-global "opaque") ≡ just (inj₁ (neutral n-global))
  opaque-choice = refl
  defined-choice :
    candidate (tm-global "defined")
      ≡ just (inj₂ (tm-atom_lit "payload" , δ refl))
  defined-choice = refl
