------------------------------------------------------------------------
-- Context lemmas.
--
-- The weakening and substitution lemmas (Proof/Preservation.agda) need
-- algebraic facts about the typing context. With the LENGTH-INDEXED context
-- of Core.Typing, lookup is a total function on `Fin n` and `extend` is
-- definitional, so the de Bruijn bookkeeping reduces to `refl`-level
-- identities.
--
-- STATUS: all lemmas in this module are PROVED.
------------------------------------------------------------------------
module Proof.Context where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Core.Syntax
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; lookup-extend)

------------------------------------------------------------------------
-- Weakening a lookup.
--
-- Extending a context with a fresh binder shifts every existing variable
-- up by one, with its type renamed by `wk`. Definitional with the
-- length-indexed context (`lookup-extend` from Core.Typing).
------------------------------------------------------------------------

lookup-weaken : ∀ {n} (Γ : Ctx n) (T : Term) (i : Fin n)
              → lookup (extend Γ T) (suc i) ≡ rename wk (lookup Γ i)
lookup-weaken = lookup-extend

------------------------------------------------------------------------
-- The head variable.
--
-- Looking up index 0 in an extended context gives the renamed fresh binder.
------------------------------------------------------------------------

lookup-head : ∀ {n} (Γ : Ctx n) (T : Term) → lookup (extend Γ T) zero ≡ rename wk T
lookup-head Γ T = refl
