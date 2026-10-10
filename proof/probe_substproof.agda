module probe_substproof where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wk; wkFin; Conversion)
open import Proof.Substitution using (subst-id; subst-var-eq; subst-var-neq; <-false)
open import Proof.Context using (lookup-head)

-- The head-only substitution lemma. Context extend Γ A, substitute index 0.
-- Statement: if extend Γ A ⊢ t ⇒ T and Γ ⊢ a ⇐ A, then Γ ⊢ substT 0 a t ⇒ substT 0 a T.
--
-- ⇒-var zero: t = var 0, T = A. substT 0 a (var 0) = a.
--   substT 0 a A: A is scoped in Γ (WfCtx), so A doesn't use index 0.
--   Wait — A is scoped in Γ, so its free vars are < lengthCtx Γ. In the
--   EXTENDED context, index 0 is the new binder. A's free vars refer to
--   indices 1..lengthCtx Γ. So A doesn't use index 0. So substT 0 a A = A.
--   Need Γ ⊢ a ⇐ A. ✓ (hypothesis).
-- ⇒-var (suc k): t = var (suc k), T = rename wk (lookup Γ k) (by lookup-extend).
--   substT 0 a (var (suc k)) = var (suc k) (index ≠ 0).
--   substT 0 a (rename wk (lookup Γ k)) = rename wk (lookup Γ k) (since
--   rename wk shifts everything, index 0 unused).
--   Need Γ ⊢ var (suc k) ⇒ rename wk (lookup Γ k). But ⇒-var k gives
--   Γ ⊢ var k ⇒ lookup Γ k. Hmm, mismatch: var (suc k) vs var k.
--
-- Wait, the term is `var (suc k)` in the extended context, and after
-- substitution it's `var (suc k)` (unchanged). But in context Γ, the variable
-- at index `suc k` doesn't exist (Γ has length k+1... no, Γ has lengthCtx Γ,
-- and k : Fin (lengthCtx Γ), so suc k : Fin (suc (lengthCtx Γ)) which is the
-- extended context's length).
--
-- So after substitution, the term `var (suc k)` lives in context Γ, but
-- index `suc k` may be out of range for Γ! Unless k is the last index.
--
-- This is the crux: substituting index 0 SHRINKS the context, and the
-- variable indices above 0 must shift DOWN by 1. So the substitution isn't
-- just `substT 0 a` on the term — the term's variables above 0 must be
-- renumbered.
