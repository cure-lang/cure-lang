------------------------------------------------------------------------
-- The fixed, small, predicative universe hierarchy Type 0 : Type 1 : Type 2
-- with cumulativity (Type i <: Type i+1).
--
-- Faithful to `Cure.Core.Universe` (lib/cure/core/universe.ex): the ceiling
-- is 2, `succ` fails past the ceiling, and `le?` is cumulative inclusion.
------------------------------------------------------------------------
module Core.Universe where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

-- Universe levels: exactly three. The kernel's `Term.term?/1` rejects any
-- `{:type, level}` with `level > 2`, so a well-formed Core term cannot carry
-- an out-of-range level. Encoding the invariant in the type makes the
-- ceiling a theorem rather than a side condition.
data Level : Set where
  l0 : Level
  l1 : Level
  l2 : Level

-- The numeric view of a level.
toNat : Level → ℕ
toNat l0 = 0
toNat l1 = 1
toNat l2 = 2

-- Every level is in range (the ceiling is now a theorem, not a predicate).
InRange : Level → Set
InRange _ = ⊤

-- The ceiling predicate retained for compatibility with the kernel's
-- `Universe.ceiling`; every level satisfies it.
in-range : (l : Level) → InRange l
in-range _ = tt

-- In-range levels have numeric value ≤ 2.
toNat≤2 : ∀ (l : Level) → toNat l ≤ 2
toNat≤2 l0 = z≤n
toNat≤2 l1 = s≤s z≤n
toNat≤2 l2 = s≤s (s≤s z≤n)

ceiling : ℕ
ceiling = 2

------------------------------------------------------------------------
-- The universe that `Type level` itself inhabits: `Type level : Type (level+1)`.
-- Fails when the successor would exceed the ceiling.
------------------------------------------------------------------------

succLevel : (l : Level) → Maybe Level
succLevel l0 = just l1
succLevel l1 = just l2
succLevel l2 = nothing

------------------------------------------------------------------------
-- Cumulativity: `l1 ≤ l2` on the numeric encoding.
------------------------------------------------------------------------

le : ℕ → ℕ → Bool
le = _≤ᵇ_

-- The semantic statement of cumulativity, on the inductive `_≤_`.
Cumulative : ℕ → ℕ → Set
Cumulative = _≤_

cumul-refl : ∀ {l} → Cumulative l l
cumul-refl = ≤-refl

cumul-suc : ∀ {l1 l2} → Cumulative l1 l2 → Cumulative l1 (suc l2)
cumul-suc z≤n = z≤n
cumul-suc (s≤s p) = s≤s (cumul-suc p)

cumul-trans : ∀ {a b c} → Cumulative a b → Cumulative b c → Cumulative a c
cumul-trans = ≤-trans

------------------------------------------------------------------------
-- The max operation used by Π/Σ formation: the universe of a type former
-- over domains at l1 and l2 is max(l1, l2).
------------------------------------------------------------------------

_⊔_ : ℕ → ℕ → ℕ
zero ⊔ n = n
suc m ⊔ zero = suc m
suc m ⊔ suc n = suc (m ⊔ n)

max : ℕ → ℕ → ℕ
max = _⊔_

max-left : ∀ m n → m ≤ max m n
max-left zero n = z≤n
max-left (suc m) zero = ≤-refl
max-left (suc m) (suc n) = s≤s (max-left m n)

max-right : ∀ m n → n ≤ max m n
max-right zero n = ≤-refl
max-right (suc m) zero = z≤n
max-right (suc m) (suc n) = s≤s (max-right m n)

max-comm : ∀ m n → max m n ≡ max n m
max-comm zero zero = refl
max-comm zero (suc n) = refl
max-comm (suc m) zero = refl
max-comm (suc m) (suc n) = cong suc (max-comm m n)

------------------------------------------------------------------------
-- Cumulativity and max on the three-element `Level` type.
--
-- These are the operations the typing judgment uses directly: Π formation
-- takes the max of the domain and codomain levels, and the cumulative
-- checking rule needs `l1 ≤ l2` on levels.
------------------------------------------------------------------------

infix 4 _≤ˡ_

data _≤ˡ_ : Level → Level → Set where
  l≤-refl : ∀ {l} → l ≤ˡ l
  l0≤l1 : l0 ≤ˡ l1
  l0≤l2 : l0 ≤ˡ l2
  l1≤l2 : l1 ≤ˡ l2

≤ˡ-trans : ∀ {a b c} → a ≤ˡ b → b ≤ˡ c → a ≤ˡ c
≤ˡ-trans l≤-refl q = q
≤ˡ-trans l0≤l1 l≤-refl = l0≤l1
≤ˡ-trans l0≤l1 l1≤l2 = l0≤l2
≤ˡ-trans l0≤l2 l≤-refl = l0≤l2
≤ˡ-trans l1≤l2 l≤-refl = l1≤l2

-- The universe of a Π over levels l1 and l2 is their max.
_⊔ˡ_ : Level → Level → Level
l0 ⊔ˡ l = l
l1 ⊔ˡ l0 = l1
l1 ⊔ˡ l1 = l1
l1 ⊔ˡ l2 = l2
l2 ⊔ˡ _ = l2

⊔ˡ-left : ∀ a b → a ≤ˡ (a ⊔ˡ b)
⊔ˡ-left l0 l0 = l≤-refl
⊔ˡ-left l0 l1 = l0≤l1
⊔ˡ-left l0 l2 = l0≤l2
⊔ˡ-left l1 l0 = l≤-refl
⊔ˡ-left l1 l1 = l≤-refl
⊔ˡ-left l1 l2 = l1≤l2
⊔ˡ-left l2 l0 = l≤-refl
⊔ˡ-left l2 l1 = l≤-refl
⊔ˡ-left l2 l2 = l≤-refl

⊔ˡ-right : ∀ a b → b ≤ˡ (a ⊔ˡ b)
⊔ˡ-right l0 l0 = l≤-refl
⊔ˡ-right l0 l1 = l≤-refl
⊔ˡ-right l0 l2 = l≤-refl
⊔ˡ-right l1 l0 = l0≤l1
⊔ˡ-right l1 l1 = l≤-refl
⊔ˡ-right l1 l2 = l≤-refl
⊔ˡ-right l2 l0 = l0≤l2
⊔ˡ-right l2 l1 = l1≤l2
⊔ˡ-right l2 l2 = l≤-refl
