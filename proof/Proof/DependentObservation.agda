------------------------------------------------------------------------
-- A computational observation policy returning ONLY actual Value/step
-- witnesses. Failure is allowed; native progress supplies the fallback.
-- This chooses a weak-head path, not normal forms or kernel NbE.
------------------------------------------------------------------------
module Proof.DependentObservation where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; _,_; ∃)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.String.Properties as String
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Reduction

-- First-match lookup carries its exact name/arity/body equation. No
-- registry-wide coverage or global literal-arity premise is assumed.
lookup-branch : ∀ name brs
  → Maybe (Σ ℕ (λ ar → Σ Term (λ b → findBranch name brs ≡ just (name , ar , b))))
lookup-branch name [] = nothing
lookup-branch name ((cn , ar , b) ∷ rest) with String._≟_ name cn
... | yes refl = just (ar , b , refl)
... | no different with lookup-branch name rest
... | nothing = nothing
... | just (size , body , found) = just (size , body , found)

module Policy (sig : Signature) where
  Choice : Term → Set
  Choice t = Value t ⊎ (∃ λ u → _⇝_ sig t u)

  -- The argument is an existing reduction constructor, not a typing or
  -- preservation callback. Both lookup and exact arity are checked here.
  choose-branch : ∀ {t} name fields brs
    → (∀ {ar b} → findBranch name brs ≡ just (name , ar , b)
        → length fields ≡ ar → _⇝_ sig t (substArgs fields b))
    → Maybe (Choice t)
  choose-branch name fields brs rule with lookup-branch name brs
  ... | nothing = nothing
  ... | just (ar , b , found) with Nat._≟_ (length fields) ar
  ... | yes size = just (inj₂ (substArgs fields b , rule found size))
  ... | no different = nothing

  candidate : ∀ t → Maybe (Choice t)
  candidate (tm-type level) = just (inj₁ (canonical c-type))
  candidate (tm-var i) = just (inj₁ (neutral n-var))
  candidate (tm-pi grade domain codomain) = just (inj₁ (canonical c-pi))
  candidate (tm-lam grade domain body) = just (inj₁ (canonical c-lam))
  candidate (tm-let grade ty value body) = just (inj₂ (substTopT value body , ζ))
  candidate (tm-app (tm-lam grade domain body) arg) = just (inj₂ (substTopT arg body , β))
  candidate (tm-app fun arg) with candidate fun
  ... | just (inj₂ (next , step)) = just (inj₂ (tm-app next arg , ξ-app₁ step))
  ... | just (inj₁ (neutral head)) = just (inj₁ (neutral (n-app head)))
  ... | _ = nothing
  candidate (tm-data name ps is) = just (inj₁ (canonical c-data))
  candidate (tm-ctor name fields) = just (inj₁ (canonical c-ctor))
  candidate (tm-case (tm-ctor name fields) mot brs) = choose-branch name fields brs ι
  candidate (tm-case (tm-nat_lit zero) mot brs) = choose-branch "Z" [] brs ι-nat-zero
  candidate (tm-case (tm-nat_lit (suc k)) mot brs) =
    choose-branch "S" (tm-nat_lit k ∷ []) brs ι-nat-suc
  candidate (tm-case (tm-bounded_lit zero) mot brs) =
    choose-branch "First" (tm-nat_lit 0 ∷ []) brs ι-bounded-zero
  candidate (tm-case (tm-bounded_lit (suc k)) mot brs) =
    choose-branch "Next" (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) brs ι-bounded-suc
  candidate (tm-case scrutinee mot brs) with candidate scrutinee
  ... | just (inj₂ (next , step)) = just (inj₂ (tm-case next mot brs , ξ-case step))
  ... | just (inj₁ (neutral head)) = just (inj₁ (neutral (n-case head)))
  ... | _ = nothing
  candidate (tm-global name) with Signature.body sig name in found
  ... | just body = just (inj₂ (body , δ found))
  ... | nothing = just (inj₁ (neutral n-global))
  candidate tm-int_type = just (inj₁ (canonical c-int_type))
  candidate (tm-int_lit value) = just (inj₁ (canonical c-int_lit))
  candidate (tm-nat_lit value) = just (inj₁ (canonical c-nat_lit))
  candidate (tm-bounded_lit value) = just (inj₁ (canonical c-bounded_lit))
  candidate tm-float_type = just (inj₁ (canonical c-float_type))
  candidate tm-float_lit = just (inj₁ (canonical c-float_lit))
  candidate tm-binary_type = just (inj₁ (canonical c-binary_type))
  candidate tm-atom_type = just (inj₁ (canonical c-atom_type))
  candidate (tm-atom_lit value) = just (inj₁ (canonical c-atom_lit))
  candidate (tm-effect_type ty) = just (inj₁ (canonical c-effect_type))
  candidate (tm-effect_pure value) = just (inj₁ (canonical c-effect_pure))
  candidate (tm-effect_bind effect continuation) = just (inj₁ (canonical c-effect_bind))
  candidate (tm-hole name) = just (inj₁ (neutral n-hole))
  candidate tm-absurd = nothing
