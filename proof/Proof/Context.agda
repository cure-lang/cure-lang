------------------------------------------------------------------------
-- Context lemmas.
--
-- The weakening and substitution lemmas (Proof/Preservation.agda) need
-- algebraic facts about the typing context. With the length-indexed
-- context of Core.Typing, lookup is a total function on `Fin`, and
-- extending prepends a binder (so existing indices shift up by one).
--
-- STATUS: all lemmas in this module are PROVED.
------------------------------------------------------------------------
module Proof.Context where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≡ᵇ_; _<_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-refl; ≤-trans; <⇒≢; ≡ᵇ⇒≡)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin)

------------------------------------------------------------------------
-- Weakening a lookup.
--
-- Extending a context with a fresh binder shifts every existing variable
-- up by one, leaving its type unchanged. With the length-indexed context
-- this is definitional (`lookup-extend` from Core.Typing, re-exported).
------------------------------------------------------------------------

lookup-weaken : ∀ {Γ} (T : Term) (i : Fin (lengthCtx Γ))
              → lookup (extend Γ T) (wkFin i) ≡ lookup Γ i
lookup-weaken T i = refl

------------------------------------------------------------------------
-- The head variable.
--
-- Looking up index 0 in an extended context gives the fresh binder's type.
------------------------------------------------------------------------

lookup-head : ∀ {Γ} (T : Term) → lookup (extend Γ T) zero ≡ T
lookup-head T = refl

------------------------------------------------------------------------
-- `toℕ (wkFin i) ≡ toℕ i + 1`.
------------------------------------------------------------------------

toℕ-wkFin : ∀ {n} (i : Fin n) → toℕ (wkFin i) ≡ toℕ i + 1
toℕ-wkFin i = trans (cong suc (sym (+-identityʳ (toℕ i)))) (sym (+-suc (toℕ i) 0))
