------------------------------------------------------------------------
-- The QTT quantity carrier.
--
-- Faithful to `Cure.Core.Grade` (lib/cure/core/grade.ex): a four-element
-- carrier {:erased, :linear, :affine, :unrestricted} = {0, 1, ≤1, ω} with
-- an additive monoid (summing usages), a multiplicative monoid (scaling a
-- context), a usage predicate `admits?`, and a subusaging preorder `leq`.
--
-- The carrier is finite, so every law is discharged by exhaustive case
-- analysis rather than assumed. This is the "Grades" item of
-- docs/SOUNDNESS.md §7.4.
------------------------------------------------------------------------
module Core.Grade where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Function using (_∘_)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _≤ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- The carrier
------------------------------------------------------------------------

data Grade : Set where
  erased linear affine unrestricted : Grade

-- Every grade, for exhaustive reasoning.
all-grades : List Grade
all-grades = erased ∷ linear ∷ affine ∷ unrestricted ∷ []

------------------------------------------------------------------------
-- Additive monoid: summing usages
--
-- `1 + 1 = ω`, not `2`: the carrier records how a binder MAY be used,
-- and "twice" is already outside every restricted grade.
------------------------------------------------------------------------

add : Grade → Grade → Grade
add erased b = b
add a erased = a
add unrestricted _ = unrestricted
add _ unrestricted = unrestricted
add linear linear = unrestricted
add linear affine = unrestricted
add affine linear = unrestricted
add affine affine = unrestricted

zeroᵍ : Grade
zeroᵍ = erased

add-zero-left : ∀ g → add zeroᵍ g ≡ g
add-zero-left g = refl

add-zero-right : ∀ g → add g zeroᵍ ≡ g
add-zero-right erased = refl
add-zero-right linear = refl
add-zero-right affine = refl
add-zero-right unrestricted = refl

add-comm : ∀ a b → add a b ≡ add b a
add-comm erased b = sym (add-zero-right b)
add-comm linear erased = refl
add-comm linear linear = refl
add-comm linear affine = refl
add-comm linear unrestricted = refl
add-comm affine erased = refl
add-comm affine linear = refl
add-comm affine affine = refl
add-comm affine unrestricted = refl
add-comm unrestricted erased = refl
add-comm unrestricted linear = refl
add-comm unrestricted affine = refl
add-comm unrestricted unrestricted = refl

------------------------------------------------------------------------
-- Multiplicative monoid: scaling a context
--
-- `0` annihilates; `1` is the identity. `affine * affine = affine` keeps
-- affinity stable under nesting.
------------------------------------------------------------------------

mul : Grade → Grade → Grade
mul erased _ = erased
mul _ erased = erased
mul linear b = b
mul a linear = a
mul affine affine = affine
mul affine unrestricted = unrestricted
mul unrestricted _ = unrestricted

oneᵍ : Grade
oneᵍ = linear

mul-one-left : ∀ g → mul oneᵍ g ≡ g
mul-one-left erased = refl
mul-one-left linear = refl
mul-one-left affine = refl
mul-one-left unrestricted = refl

mul-one-right : ∀ g → mul g oneᵍ ≡ g
mul-one-right erased = refl
mul-one-right linear = refl
mul-one-right affine = refl
mul-one-right unrestricted = refl

mul-zero-left : ∀ g → mul zeroᵍ g ≡ zeroᵍ
mul-zero-left g = refl

mul-zero-right : ∀ g → mul g zeroᵍ ≡ zeroᵍ
mul-zero-right erased = refl
mul-zero-right linear = refl
mul-zero-right affine = refl
mul-zero-right unrestricted = refl

------------------------------------------------------------------------
-- The usage rule: does `declared` admit exactly `used` occurrences?
--
-- Generalises Idris's `checkUsageOK`; this is where affinity differs
-- from linearity.
------------------------------------------------------------------------

infix 4 _admits_

_admits_ : Grade → ℕ → Bool
erased admits used = used ≡ᵇ 0
linear admits used = used ≡ᵇ 1
affine admits used = used ≤ᵇ 1
unrestricted admits used = true

------------------------------------------------------------------------
-- The preorder: subusaging
--
-- `leq a b` means a value used with grade `a` is acceptable where grade
-- `b` was declared. `unrestricted` is the top.
------------------------------------------------------------------------

infix 4 _≤ᵍ_

data _≤ᵍ_ : Grade → Grade → Set where
  ≤-refl : ∀ {g} → g ≤ᵍ g
  ≤-top : ∀ {g} → g ≤ᵍ unrestricted
  ≤-erased-affine : erased ≤ᵍ affine
  ≤-linear-affine : linear ≤ᵍ affine

≤ᵍ-refl : ∀ {g} → g ≤ᵍ g
≤ᵍ-refl = ≤-refl

≤ᵍ-trans : ∀ {a b c} → a ≤ᵍ b → b ≤ᵍ c → a ≤ᵍ c
≤ᵍ-trans ≤-refl q = q
≤ᵍ-trans ≤-top ≤-refl = ≤-top
≤ᵍ-trans ≤-top ≤-top = ≤-top
≤ᵍ-trans ≤-erased-affine ≤-refl = ≤-erased-affine
≤ᵍ-trans ≤-erased-affine ≤-top = ≤-top
≤ᵍ-trans ≤-linear-affine ≤-refl = ≤-linear-affine
≤ᵍ-trans ≤-linear-affine ≤-top = ≤-top

≤ᵍ-top : ∀ {g} → g ≤ᵍ unrestricted
≤ᵍ-top = ≤-top

------------------------------------------------------------------------
-- Predicates
------------------------------------------------------------------------

erased? : Grade → Bool
erased? erased = true
erased? linear = false
erased? affine = false
erased? unrestricted = false

present? : Grade → Bool
present? = not ∘ erased?

restricted? : Grade → Bool
restricted? unrestricted = false
restricted? erased = true
restricted? linear = true
restricted? affine = true

-- A grade is `erased` exactly when it is definitionally `zeroᵍ`.
erased≡zero : ∀ {g} → erased? g ≡ true → g ≡ erased
erased≡zero {erased} p = refl
erased≡zero {linear} ()
erased≡zero {affine} ()
erased≡zero {unrestricted} ()
