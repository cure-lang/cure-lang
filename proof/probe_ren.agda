module probe_ren where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax

-- The "shift down" renaming: index 0 ↦ 0, suc k ↦ k. This removes a binder.
pred-ren : Ren
pred-ren zero = zero
pred-ren (suc k) = k
