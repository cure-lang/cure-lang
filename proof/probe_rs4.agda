module probe_rs4 where
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; +-suc; +-identityʳ; +-comm; ≤-refl; ≤-trans; n≤1+n; +-monoʳ-≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax

Monotone : Ren → Set
Monotone ρ = ∀ {k k'} → k ≤ k' → ρ k ≤ ρ k'

-- ρ k ≥ k for the identity-like renamings (needed so c ≤ k ⟹ c ≤ ρ k).
Above : Ren → Set
Above ρ = ∀ k → k ≤ ρ k

ext-mono : ∀ {ρ} → Monotone ρ → Monotone (ext ρ)
ext-mono mono z≤n = z≤n
ext-mono mono (s≤s p) = s≤s (mono p)

ext-above : ∀ {ρ} → Above ρ → Above (ext ρ)
ext-above ab zero = z≤n
ext-above ab (suc k) = s≤s (ab k)

-- The key: c ≤ k ⟹ c ≤ ρ k, given Above ρ.
above-le : ∀ {ρ} → Above ρ → ∀ {c k} → c ≤ k → c ≤ ρ k
above-le ab c≤k = ≤-trans c≤k (ab _)

-- General rename-shift with monotone, above-identity ρ.
-- rename (ext^ a ρ) (shift a c t) ≡ shift a c (rename ρ t)
