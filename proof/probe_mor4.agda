module probe_mor4 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Typing using (Context; _∋_at_; here; there; extend)

-- The target context is built by recursion on the source, inserting the
-- type renamed by the morphism's OWN renaming at each binder.
record Mor (ρ : Ren) : Set₁ where
  field
    target : Context → Context
    lookup : ∀ {Γ T k} → Γ ∋ T at k → target Γ ∋ rename ρ T at ρ k

open Mor

-- Under a binder: the head type T is renamed by ρ (the ambient renaming),
-- and the rest by the extended renaming... but the target function is
-- indexed only by ρ. So we need `target` to take the renaming too.
