module probe_s where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wk; wkFin; Conversion)
open import Proof.Substitution using (subst-id)
open import Proof.Context using (lookup-head; lookup-extend)

-- The ⇒-var zero case of the substitution lemma.
-- Context: extend Γ A. Term: var 0. Type: lookup (extend Γ A) zero = A.
-- substTop a (var 0) = substS (topSub a) (var 0) = topSub a 0 = a.
-- substTop a A = substS (topSub a) A. Since A is scoped in Γ (WfCtx), and
-- in the extended context A's free vars are >= 1 (the global convention
-- renamed them by wk), topSub a maps them to k-1... 
-- Hmm, A's free vars in extend Γ A: A was scoped in Γ, and extend renamed
-- it by wk, so A's free vars are suc k for k < lengthCtx Γ. topSub a (suc k) = var k.
-- So substTop a A = rename pred A (roughly). NOT A!
--
-- Wait: WfCtx (extend Γ A) says Scoped (lengthCtx Γ) A. But the STORED type
-- at index 0 is A (not renamed). Hmm, extend Γ A = renameCtx wk Γ ▷ A, so the
-- head is A, unrenamed. So lookup (extend Γ A) zero = A.
-- And A is scoped in Γ, so Scoped (lengthCtx Γ) A. Its free vars are < lengthCtx Γ.
-- topSub a (suc k) = tm-var k for k < lengthCtx Γ. So substTop a A = A with
-- each free var k ↦ k. So substTop a A = A!
--
-- Wait, A's free vars are < lengthCtx Γ, so they're k for k < lengthCtx Γ,
-- and topSub a k for k >= 1 is tm-var (k-1). But A's free vars include 0!
-- A is scoped in Γ, so it can use index 0 (the head of Γ).
-- In the extended context, A's free var 0 refers to... the head of Γ, which
-- is now at index 1 in extend Γ A. So A must be renamed by wk when stored!
