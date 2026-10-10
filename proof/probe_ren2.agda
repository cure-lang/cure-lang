module probe_ren2 where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Core.Syntax

-- Key: `rename (ext ρ) (shift 1 0 t) ≡ shift 1 0 (rename ρ t)`? Not quite.
-- Standard: shift is `rename (λ k → k + 1)`.
-- Let's define shift via rename and prove the interaction.

-- `shift a c` is `rename (λ k → if c ≤ᵇ k then k + a else k)`... but under binders
-- the cutoff changes. Let's instead prove the general renaming/subst law directly.

-- First: rename is functorial: rename ρ (rename σ t) ≡ rename (ρ ∘ σ) t
-- (with the ext handling).
