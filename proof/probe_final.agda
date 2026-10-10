module probe_final where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wk; wkFin; Conversion)
open import Proof.Substitution using (subst-id)
open import Proof.Context using (lookup-head; lookup-extend)

-- topSub a: 0 ↦ a, suc k ↦ var k.
topSub : Term → Sub
topSub a zero = a
topSub a (suc k) = tm-var k

-- Key: substS (topSub a) (rename wk T) ≡ T when T is scoped in Γ.
-- rename wk T has free vars suc k for k free in T. topSub a (suc k) = var k.
-- So substS (topSub a) (rename wk T) = T (with k ↦ k).
-- This is a lemma: substS (topSub a) (rename wk T) ≡ T for T scoped appropriately.
