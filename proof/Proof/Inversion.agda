------------------------------------------------------------------------
-- Canonical inversion by induction on typing, accumulating conversion.
-- Intermediate result types need not expose any particular raw head.
-- Only introduction rules compare TWO rigid heads. These are conditional
-- derivations over Conversion, not a proof of executable NbE correctness.
------------------------------------------------------------------------
module Proof.Inversion where

open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.Product using (Σ; _×_; _,_; ∃)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (Grade)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion)
open import Proof.Values using (Canonical)

IsLam : Term → Set
IsLam t = Σ Grade (λ g → Σ Term (λ d → Σ Term (λ b → t ≡ tm-lam g d b)))

IsDataValue : Term → Set
IsDataValue t =
    (Σ Name (λ c → Σ (List Term) (λ args → t ≡ tm-ctor c args)))
  ⊎ (Σ ℕ (λ m → t ≡ tm-nat_lit m))
  ⊎ (Σ ℕ (λ b → t ≡ tm-bounded_lit b))

module Invert (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.Typing.Typing ind sig conv

  private
    infix 4 _∼_
    _∼_ = Conversion._≈_ conv
    reflexive = Conversion.≈-refl conv
    compose = Conversion.≈-trans conv

  rigid-clash : ∀ {t u h h′}
    → HasTypeHead t h → HasTypeHead u h′
    → (h ≡ h′ → ⊥) → t ∼ u → ⊥
  rigid-clash ht hu unequal eq =
    unequal (Conversion.≈-heads conv ht hu eq)

  universe-not-pi : ∀ {l g d c} → tm-type l ∼ tm-pi g d c → ⊥
  universe-not-pi = rigid-clash ty-universe ty-pi (λ ())

  invert-pi-conv : ∀ {k} {Γ : Ctx k} {t T g d c}
    → Canonical t → Γ ⊢ t ⇒ T → T ∼ tm-pi g d c → IsLam t
  invert-pi-conv c-type (⇒-type p) eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-pi (⇒-pi p q) eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-lam (⇒-lam p q) eq = _ , _ , _ , refl
  invert-pi-conv c-data (⇒-data p q r) eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-ctor (⇒-ctor p q) eq =
    ⊥-elim (rigid-clash ty-data ty-pi (λ ()) eq)
  invert-pi-conv c-int_type ⇒-int_type eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-int_lit ⇒-int_lit eq =
    ⊥-elim (rigid-clash ty-int ty-pi (λ ()) eq)
  invert-pi-conv c-nat_lit (⇒-nat_lit p) eq =
    ⊥-elim (rigid-clash ty-data ty-pi (λ ()) eq)
  invert-pi-conv c-bounded_lit (⇒-bounded_lit p) eq =
    ⊥-elim (rigid-clash ty-data ty-pi (λ ()) eq)
  invert-pi-conv c-float_type ⇒-float_type eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-float_lit ⇒-float_lit eq =
    ⊥-elim (rigid-clash ty-float ty-pi (λ ()) eq)
  invert-pi-conv c-binary_type ⇒-binary_type eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-atom_type ⇒-atom_type eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-atom_lit ⇒-atom_lit eq =
    ⊥-elim (rigid-clash ty-atom ty-pi (λ ()) eq)
  invert-pi-conv c-effect_type (⇒-effect_type p) eq = ⊥-elim (universe-not-pi eq)
  invert-pi-conv c-effect_pure (⇒-effect_pure p) eq =
    ⊥-elim (rigid-clash ty-effect ty-pi (λ ()) eq)
  invert-pi-conv c-effect_bind (⇒-effect_bind p q) eq =
    ⊥-elim (rigid-clash ty-effect ty-pi (λ ()) eq)
  invert-pi-conv can (⇒-conv der eq′) eq =
    invert-pi-conv can der (compose eq′ eq)
  invert-pi-conv can (⇒-cumul der le) eq = ⊥-elim (universe-not-pi eq)

  invert-pi : ∀ {k} {Γ : Ctx k} {t g d c}
    → Canonical t → Γ ⊢ t ⇒ tm-pi g d c → IsLam t
  invert-pi can der = invert-pi-conv can der reflexive

  invert-data-conv : ∀ {k} {Γ : Ctx k} {t T n ps is}
    → Canonical t → Γ ⊢ t ⇒ T → T ∼ tm-data n ps is → IsDataValue t
  invert-data-conv c-type (⇒-type p) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-pi (⇒-pi p q) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-lam (⇒-lam p q) eq =
    ⊥-elim (rigid-clash ty-pi ty-data (λ ()) eq)
  invert-data-conv c-data (⇒-data p q r) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-ctor (⇒-ctor p q) eq = inj₁ (_ , _ , refl)
  invert-data-conv c-int_type ⇒-int_type eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-int_lit ⇒-int_lit eq =
    ⊥-elim (rigid-clash ty-int ty-data (λ ()) eq)
  invert-data-conv c-nat_lit (⇒-nat_lit p) eq = inj₂ (inj₁ (_ , refl))
  invert-data-conv c-bounded_lit (⇒-bounded_lit p) eq = inj₂ (inj₂ (_ , refl))
  invert-data-conv c-float_type ⇒-float_type eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-float_lit ⇒-float_lit eq =
    ⊥-elim (rigid-clash ty-float ty-data (λ ()) eq)
  invert-data-conv c-binary_type ⇒-binary_type eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-atom_type ⇒-atom_type eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-atom_lit ⇒-atom_lit eq =
    ⊥-elim (rigid-clash ty-atom ty-data (λ ()) eq)
  invert-data-conv c-effect_type (⇒-effect_type p) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-conv c-effect_pure (⇒-effect_pure p) eq =
    ⊥-elim (rigid-clash ty-effect ty-data (λ ()) eq)
  invert-data-conv c-effect_bind (⇒-effect_bind p q) eq =
    ⊥-elim (rigid-clash ty-effect ty-data (λ ()) eq)
  invert-data-conv can (⇒-conv der eq′) eq =
    invert-data-conv can der (compose eq′ eq)
  invert-data-conv can (⇒-cumul der le) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)

  invert-data : ∀ {k} {Γ : Ctx k} {t n ps is}
    → Canonical t → Γ ⊢ t ⇒ tm-data n ps is → IsDataValue t
  invert-data can der = invert-data-conv can der reflexive

  conv-pi-components : ∀ {g d c g′ d′ c′}
    → tm-pi g′ d′ c′ ∼ tm-pi g d c
    → g′ ≡ g × (d′ ∼ d) × (c′ ∼ c)
  conv-pi-components = Conversion.≈-pi-components conv

  invert-data-check-conv : ∀ {k} {Γ : Ctx k} {t T n ps is}
    → Γ ⊢ t ⇐ T → Canonical t → T ∼ tm-data n ps is → IsDataValue t
  invert-data-check-conv (⇐-lam ds body) can eq =
    ⊥-elim (rigid-clash ty-pi ty-data (λ ()) eq)
  invert-data-check-conv (⇐-infer der eq′) can eq =
    invert-data-conv can der (compose eq′ eq)
  invert-data-check-conv (⇐-conv der eq′) can eq =
    invert-data-check-conv der can (compose eq′ eq)
  invert-data-check-conv (⇐-cumul der le) can eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)
  invert-data-check-conv ⇐-hole () eq

  invert-data-check : ∀ (k : ℕ) (Γ : Ctx k) {t n ps is}
    → Γ ⊢ t ⇐ tm-data n ps is → Canonical t → IsDataValue t
  invert-data-check _ _ der can = invert-data-check-conv der can reflexive

  invert-pi-check-conv : ∀ {k} {Γ : Ctx k} {t T g d c}
    → Γ ⊢ t ⇐ T → Canonical t → T ∼ tm-pi g d c → IsLam t
  invert-pi-check-conv (⇐-lam ds body) can eq = _ , _ , _ , refl
  invert-pi-check-conv (⇐-infer der eq′) can eq =
    invert-pi-conv can der (compose eq′ eq)
  invert-pi-check-conv (⇐-conv der eq′) can eq =
    invert-pi-check-conv der can (compose eq′ eq)
  invert-pi-check-conv (⇐-cumul der le) can eq = ⊥-elim (universe-not-pi eq)
  invert-pi-check-conv ⇐-hole () eq

  invert-pi-check : ∀ (k : ℕ) (Γ : Ctx k) {t g d c}
    → Γ ⊢ t ⇐ tm-pi g d c → Canonical t → IsLam t
  invert-pi-check _ _ der can = invert-pi-check-conv der can reflexive

  -- Metadata extraction uses the same accumulator. Equal exposed data
  -- heads preserve the family NAME even through non-rigid intermediate T.
  constructor-data-conv : ∀ {k} {Γ : Ctx k} {c args T n ps is}
    → Γ ⊢ tm-ctor c args ⇒ T → T ∼ tm-data n ps is
    → ∃ λ f → ∃ λ ct
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      × fam-name f ≡ n × (Γ ⊢* args ⇐* ctor-args ct)
  constructor-data-conv (⇒-ctor fc sp) eq =
    _ , _ , fc , data-head-injective (Conversion.≈-heads conv ty-data ty-data eq) , sp
  constructor-data-conv (⇒-conv der eq′) eq =
    constructor-data-conv der (compose eq′ eq)
  constructor-data-conv (⇒-cumul der le) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)

  constructor-data : ∀ {k} {Γ : Ctx k} {c args n ps is}
    → Γ ⊢ tm-ctor c args ⇒ tm-data n ps is
    → ∃ λ f → ∃ λ ct
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      × fam-name f ≡ n × (Γ ⊢* args ⇐* ctor-args ct)
  constructor-data der = constructor-data-conv der reflexive

  nat-data-family-conv : ∀ {k} {Γ : Ctx k} {m T n ps is}
    → Γ ⊢ tm-nat_lit m ⇒ T → T ∼ tm-data n ps is
    → IndEnv.builtins ind "nat" ≡ just n
  nat-data-family-conv (⇒-nat_lit builtin) eq
    with data-head-injective (Conversion.≈-heads conv ty-data ty-data eq)
  ... | refl = builtin
  nat-data-family-conv (⇒-conv der eq′) eq =
    nat-data-family-conv der (compose eq′ eq)
  nat-data-family-conv (⇒-cumul der le) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)

  nat-data-family : ∀ {k} {Γ : Ctx k} {m n ps is}
    → Γ ⊢ tm-nat_lit m ⇒ tm-data n ps is
    → IndEnv.builtins ind "nat" ≡ just n
  nat-data-family der = nat-data-family-conv der reflexive

  bounded-data-family-conv : ∀ {k} {Γ : Ctx k} {m T n ps is}
    → Γ ⊢ tm-bounded_lit m ⇒ T → T ∼ tm-data n ps is
    → IndEnv.builtins ind "bounded" ≡ just n
  bounded-data-family-conv (⇒-bounded_lit builtin) eq
    with data-head-injective (Conversion.≈-heads conv ty-data ty-data eq)
  ... | refl = builtin
  bounded-data-family-conv (⇒-conv der eq′) eq =
    bounded-data-family-conv der (compose eq′ eq)
  bounded-data-family-conv (⇒-cumul der le) eq =
    ⊥-elim (rigid-clash ty-universe ty-data (λ ()) eq)

  bounded-data-family : ∀ {k} {Γ : Ctx k} {m n ps is}
    → Γ ⊢ tm-bounded_lit m ⇒ tm-data n ps is
    → IndEnv.builtins ind "bounded" ≡ just n
  bounded-data-family der = bounded-data-family-conv der reflexive
