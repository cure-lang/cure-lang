------------------------------------------------------------------------
-- Context lemmas.
--
-- The weakening and substitution lemmas (Proof/Preservation.agda) need
-- algebraic facts about the typing context. With the length-indexed
-- context of Core.Typing, lookup is a total function on `Fin`, so the
-- de Bruijn bookkeeping reduces to `refl`-level identities.
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
-- this is definitional.
------------------------------------------------------------------------

lookup-extend : ∀ {Γ} (T : Term) (i : Fin (lengthCtx Γ))
              → lookup (extend Γ T) (wkFin i) ≡ lookup Γ i
lookup-extend T i = refl

------------------------------------------------------------------------
-- The lookup/substitution correspondence.
--
-- For the `⇒-var` case of `subst⇒`: looking up a non-head variable is
-- unaffected by substituting the head. Definitional with the function
-- lookup.
------------------------------------------------------------------------

lookup-tail : ∀ {Γ} (A : Term) (i : Fin (lengthCtx Γ))
            → lookup (extend Γ A) (suc i) ≡ lookup Γ i
lookup-tail A i = refl

------------------------------------------------------------------------
-- `suc` on `Fin` indices.
--
-- `toℕ (wkFin i) ≡ toℕ i + 1`: the weakened index is one higher.
------------------------------------------------------------------------

toℕ-wkFin : ∀ {n} (i : Fin n) → toℕ (wkFin i) ≡ toℕ i + 1
toℕ-wkFin i = trans (cong suc (sym (+-identityʳ (toℕ i)))) (sym (+-suc (toℕ i) 0))
