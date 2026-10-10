------------------------------------------------------------------------
-- Substitution infrastructure.
--
-- The β and ζ cases of Preservation (docs/SOUNDNESS.md §4) need a
-- substitution lemma: if `Γ , x : A ⊢ b : B` and `Γ ⊢ a : A`, then
-- `Γ ⊢ b[x := a] : B[x := a]`. That lemma in turn needs the algebraic
-- properties of `shift` and `substT` established here.
--
-- This module proves the *syntactic* laws (shift/subst interaction). The
-- typing-level substitution lemma is stated in Proof/Preservation.agda,
-- because it depends on the typing judgment.
--
-- STATUS: the shift/subst laws are the current work; the ones proved so
-- far are marked. The remaining goals are stated with their strategies.
------------------------------------------------------------------------
module Proof.Substitution where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Core.Syntax

-- Three-argument congruence (not in the stdlib under this name).
cong₃ : ∀ {A B C D : Set} {a a′ : A} {b b′ : B} {c c′ : C}
     → (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- `n + 0 ≡ n`
------------------------------------------------------------------------

+-zero : ∀ n → n + 0 ≡ n
+-zero = +-identityʳ

------------------------------------------------------------------------
-- Shifting by 0 is the identity, at any cutoff.
--
-- This is the base case for the subst laws: `shift 0 c t ≡ t`.
------------------------------------------------------------------------

mutual
  shiftTerms-0 : ∀ c (ts : List Term) → shiftTerms 0 c ts ≡ ts
  shiftTerms-0 c [] = refl
  shiftTerms-0 c (x ∷ xs) = cong₂ _∷_ (shift-0 c x) (shiftTerms-0 c xs)

  shiftBranches-0 : ∀ c (bs : List Branch) → shiftBranches 0 c bs ≡ bs
  shiftBranches-0 c [] = refl
  shiftBranches-0 c (x ∷ xs) = cong₂ _∷_ (shiftBranch-0 c x) (shiftBranches-0 c xs)

  shiftBranch-0 : ∀ c (b : Branch) → shiftBranch 0 c b ≡ b
  shiftBranch-0 c (cn , ar , b) = cong (λ x → cn , ar , x) (shift-0 (c + ar) b)

  shift-0 : ∀ c (t : Term) → shift 0 c t ≡ t
  shift-0 c (tm-type l) = refl
  shift-0 c (tm-var k) with c ≤ᵇ k
  ... | true  = cong tm-var (+-zero k)
  ... | false = refl
  shift-0 c (tm-pi g d b) = cong₂ (tm-pi g) (shift-0 c d) (shift-0 (suc c) b)
  shift-0 c (tm-lam g d b) = cong₂ (tm-lam g) (shift-0 c d) (shift-0 (suc c) b)
  shift-0 c (tm-let g ty v b) = cong₃ (tm-let g) (shift-0 c ty) (shift-0 c v) (shift-0 (suc c) b)
  shift-0 c (tm-app f a) = cong₂ tm-app (shift-0 c f) (shift-0 c a)
  shift-0 c (tm-data n ps is) = cong₂ (tm-data n) (shiftTerms-0 c ps) (shiftTerms-0 c is)
  shift-0 c (tm-ctor n args) = cong (tm-ctor n) (shiftTerms-0 c args)
  shift-0 c (tm-case s m brs) = cong₃ tm-case (shift-0 c s) (shift-0 c m) (shiftBranches-0 c brs)
  shift-0 c (tm-global n) = refl
  shift-0 c (tm-int_type) = refl
  shift-0 c (tm-int_lit k) = refl
  shift-0 c (tm-nat_lit k) = refl
  shift-0 c (tm-bounded_lit k) = refl
  shift-0 c (tm-float_type) = refl
  shift-0 c (tm-float_lit) = refl
  shift-0 c (tm-binary_type) = refl
  shift-0 c (tm-atom_type) = refl
  shift-0 c (tm-atom_lit n) = refl
  shift-0 c (tm-effect_type t) = cong tm-effect_type (shift-0 c t)
  shift-0 c (tm-effect_pure t) = cong tm-effect_pure (shift-0 c t)
  shift-0 c (tm-effect_bind e k) = cong₂ tm-effect_bind (shift-0 c e) (shift-0 c k)
  shift-0 c (tm-hole n) = refl
  shift-0 c (tm-absurd) = refl
