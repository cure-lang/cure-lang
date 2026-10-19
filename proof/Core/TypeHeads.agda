------------------------------------------------------------------------
-- Rigid TYPE heads: only compare heads when both terms already expose
-- type formers. There is no claim that an arbitrary converted raw term
-- has the same syntax (a let may reduce to a Pi, for example).
------------------------------------------------------------------------
module Core.TypeHeads where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Universe using (Level)

data TypeHead : Set where
  h-pi h-int h-float h-binary h-atom h-effect : TypeHead
  h-universe : Level → TypeHead
  h-data : Name → TypeHead

data HasTypeHead : Term → TypeHead → Set where
  ty-universe : ∀ {l} → HasTypeHead (tm-type l) (h-universe l)
  ty-pi : ∀ {g d c} → HasTypeHead (tm-pi g d c) h-pi
  ty-data : ∀ {name ps is} → HasTypeHead (tm-data name ps is) (h-data name)
  ty-int : HasTypeHead tm-int_type h-int
  ty-float : HasTypeHead tm-float_type h-float
  ty-binary : HasTypeHead tm-binary_type h-binary
  ty-atom : HasTypeHead tm-atom_type h-atom
  ty-effect : ∀ {a} → HasTypeHead (tm-effect_type a) h-effect

type-head-unique : ∀ {t h h′} → HasTypeHead t h → HasTypeHead t h′ → h ≡ h′
type-head-unique ty-universe ty-universe = refl
type-head-unique ty-pi ty-pi = refl
type-head-unique ty-data ty-data = refl
type-head-unique ty-int ty-int = refl
type-head-unique ty-float ty-float = refl
type-head-unique ty-binary ty-binary = refl
type-head-unique ty-atom ty-atom = refl
type-head-unique ty-effect ty-effect = refl

data-head-injective : ∀ {n m} → h-data n ≡ h-data m → n ≡ m
data-head-injective refl = refl

universe-head-injective : ∀ {i j} → h-universe i ≡ h-universe j → i ≡ j
universe-head-injective refl = refl
