module probe_rs3 where
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; +-monoˡ-≤; +-suc; +-identityʳ; +-comm; ≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Core.Syntax

-- If ρ is monotone and ρ k ≥ k, then c ≤ k implies c ≤ ρ k.
-- We need the general rename-shift with a monotone ρ.
