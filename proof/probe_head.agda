module probe_head where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin)

-- The head-only substitution lemma: context extend Γ A, substitute index 0.
-- Statement: if extend Γ A ⊢ t ⇒ T and Γ ⊢ a ⇐ A, then Γ ⊢ substT 0 a t ⇒ substT 0 a T.
--
-- ⇒-var zero: t = var 0, T = A. substT 0 a (var 0) = a, substT 0 a A.
--   Need Γ ⊢ a ⇐ substT 0 a A. Since A is scoped in Γ (WfCtx), and
--   substT 0 a A = A when A is 0-scoped... but A is scoped in Γ, so its
--   free vars are < lengthCtx Γ, which in the extended context are indices
--   1.. So A is NOT 0-scoped in the extended context; it's `Scoped 0 A`
--   only if A is closed. Hmm.
--
-- Wait: WfCtx (extend Γ A) requires Scoped (lengthCtx Γ) A. And substT 0 a A
-- is A with index 0 replaced. But A's free vars are < lengthCtx Γ, and index 0
-- in the extended context is the NEW binder. So A doesn't use index 0 (its
-- free vars are 1..lengthCtx Γ in the extended context? No — A is scoped in Γ,
-- so its free vars are 0..lengthCtx Γ - 1, which in the EXTENDED context refer
-- to indices 1..lengthCtx Γ).
--
-- This is the shift issue again: A scoped in Γ, placed in extend Γ A, has its
-- free vars at 0..lengthCtx Γ - 1, but they should be at 1..lengthCtx Γ.
-- So A must be SHIFTED when stored. This is the global convention.
