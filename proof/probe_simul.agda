module probe_simul where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax

-- Simultaneous substitution: a function from source indices to terms.
Sub : Set
Sub = ℕ → Term

-- Apply a simultaneous substitution to a term.
-- Under a binder, the substitution is extended: index 0 ↦ var 0, suc k ↦ shift 1 0 (σ k).
-- This is the standard "substitution as a function" operation.
extSub : Sub → Sub
extSub σ zero = tm-var zero
extSub σ (suc k) = shift 1 0 (σ k)
