------------------------------------------------------------------------
-- Context substitution.
--
-- The substitution lemma (Proof/Preservation.agda) needs to remove a
-- variable from the context and adjust the types above it. This module
-- provides the context surgery and its lookup law.
--
-- `removeAt Γ j` removes the variable at de Bruijn index `j` from `Γ`.
-- `embedFin Γ j` embeds the surviving indices back into `Γ`, skipping `j`.
-- The lookup law `lookup (removeAt Γ j) i ≡ lookup Γ (embedFin Γ j i)` is
-- what lets the `⇒-var` cases of the substitution lemma go through.
--
-- STATUS: all lemmas in this module are PROVED.
------------------------------------------------------------------------
module Proof.ContextSubst where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin)

------------------------------------------------------------------------
-- Removing a variable from a context.
------------------------------------------------------------------------

removeAt : Context → ℕ → Context
removeAt ⟨⟩ j = ⟨⟩
removeAt (Γ ▷ T) zero = Γ
removeAt (Γ ▷ T) (suc j) = removeAt Γ j ▷ T

------------------------------------------------------------------------
-- The index embedding: surviving indices embed into the original context,
-- skipping the removed one.
------------------------------------------------------------------------

embedFin : ∀ Γ j → Fin (lengthCtx (removeAt Γ j)) → Fin (lengthCtx Γ)
embedFin ⟨⟩ j ()
embedFin (Γ ▷ T) zero i = suc i
embedFin (Γ ▷ T) (suc j) zero = zero
embedFin (Γ ▷ T) (suc j) (suc i) = suc (embedFin Γ j i)

------------------------------------------------------------------------
-- The lookup law.
------------------------------------------------------------------------

lookup-remove : ∀ {Γ j} (i : Fin (lengthCtx (removeAt Γ j)))
              → lookup (removeAt Γ j) i ≡ lookup Γ (embedFin Γ j i)
lookup-remove {⟨⟩} {j} ()
lookup-remove {Γ ▷ T} {zero} i = refl
lookup-remove {Γ ▷ T} {suc j} zero = refl
lookup-remove {Γ ▷ T} {suc j} (suc i) = lookup-remove {Γ} {j} i
