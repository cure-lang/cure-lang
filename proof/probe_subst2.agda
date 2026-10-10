module probe_subst2 where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin)

-- The general substitution lemma. Substitute index j with term a.
-- Context: Γ has A at index j (Γ ∋ A at j).
-- Statement: if Γ ⊢ t ⇒ T and Γ ∋ A at j and Γ ⊢ a ⇐ A, then
--   Γ ⊢ substT j a t ⇒ substT j a T.
-- Under a binder: j becomes suc j, and a is shifted.
--
-- The ⇒-var case at index k:
--   if k = j: t = var j, T = A. substT j a (var j) = a, substT j a A.
--     Need Γ ⊢ a ⇐ substT j a A. Since A is the type at index j, and A is
--     scoped in the prefix below j (well-formedness), substT j a A = A.
--   if k ≠ j: t = var k, T = lookup Γ k. substT j a (var k) = var k.
--     Need Γ ⊢ var k ⇒ substT j a (lookup Γ k). Since lookup Γ k is scoped
--     appropriately and doesn't mention j... needs k ≠ j and well-formedness.
