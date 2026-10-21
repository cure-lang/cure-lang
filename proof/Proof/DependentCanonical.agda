------------------------------------------------------------------------
-- Canonical heads derived solely from native typing.
------------------------------------------------------------------------
module Proof.DependentCanonical where

open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Data.Product using (Σ; ∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Core.Syntax
open import Core.Grade using (Grade)
open import Core.Signature
open import Core.TypeHeads
open import Core.Typing using (Ctx; Conversion)
open import Core.Reduction using (Signature)
open import Core.DependentTyping
import Proof.DependentConstructorInversion as CI

Lambda : Term → Set
Lambda v = Σ Grade λ g → ∃ λ d → ∃ λ b → v ≡ tm-lam g d b

ConstructorLike : Term → Set
ConstructorLike v =
  (Σ Name λ c → Σ (List Term) λ args → v ≡ tm-ctor c args)
  ⊎ (Σ ℕ λ k → v ≡ tm-nat_lit k)
  ⊎ (Σ ℕ λ k → v ≡ tm-bounded_lit k)

Shape : TypeHead → Term → Set
Shape h-pi v = Lambda v
Shape (h-data name) v = ConstructorLike v
Shape h-int v = ⊤
Shape h-float v = ⊤
Shape h-binary v = ⊤
Shape h-atom v = ⊤
Shape h-effect v = ⊤
Shape (h-universe l) v = ⊤

module Laws (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.DependentTyping.Typing ind sig conv
  open Conversion conv
  open CI.Laws ind sig conv using (data-not-sort)

  record Principal (v A : Term) : Set where
    constructor principal
    field
      type : Term
      head : TypeHead
      rigid : HasTypeHead type head
      equal : type ≈ A
      shape : Shape head v

  abstract
    -- A cumulative conclusion has a universe head even if its premise
    -- passed through arbitrarily many non-rigid conversion intermediates.
    canonical-principal : ∀ {n} {Γ : Ctx n} {v A}
      → Γ ⊢ v ⇒ A → Canonical v → Principal v A
    canonical-principal (⇒-type p) c-type = principal _ _ ty-universe ≈-refl tt
    canonical-principal (⇒-pi p q) c-pi = principal _ _ ty-universe ≈-refl tt
    canonical-principal (⇒-lam {g = g} {d = d} {b = b} p q) c-lam =
      principal _ _ ty-pi ≈-refl (g , d , b , refl)
    canonical-principal (⇒-var i) ()
    canonical-principal (⇒-app p q) ()
    canonical-principal (⇒-let p q r) ()
    canonical-principal (⇒-global p) ()
    canonical-principal ⇒-int_type c-int_type = principal _ _ ty-universe ≈-refl tt
    canonical-principal ⇒-float_type c-float_type = principal _ _ ty-universe ≈-refl tt
    canonical-principal ⇒-binary_type c-binary_type = principal _ _ ty-universe ≈-refl tt
    canonical-principal ⇒-atom_type c-atom_type = principal _ _ ty-universe ≈-refl tt
    canonical-principal ⇒-int_lit c-int_lit = principal _ _ ty-int ≈-refl tt
    canonical-principal ⇒-float_lit c-float_lit = principal _ _ ty-float ≈-refl tt
    canonical-principal ⇒-atom_lit c-atom_lit = principal _ _ ty-atom ≈-refl tt
    canonical-principal (⇒-nat_lit {k = k} p q r s) c-nat_lit =
      principal _ _ ty-data ≈-refl (inj₂ (inj₁ (k , refl)))
    canonical-principal (⇒-bounded_lit {k = k} p q r s) c-bounded_lit =
      principal _ _ ty-data ≈-refl (inj₂ (inj₂ (k , refl)))
    canonical-principal (⇒-data p q r) c-data = principal _ _ ty-universe ≈-refl tt
    canonical-principal (⇒-ctor {name = c} {args = args} p q r) c-ctor =
      principal _ _ ty-data ≈-refl (inj₁ (c , args , refl))
    canonical-principal (⇒-case p q r s t u v w) ()
    canonical-principal (⇒-effect_type p) c-effect_type =
      principal _ _ ty-universe ≈-refl tt
    canonical-principal (⇒-effect_pure p) c-effect_pure =
      principal _ _ ty-effect ≈-refl tt
    canonical-principal (⇒-effect_bind p q) c-effect_bind =
      principal _ _ ty-effect ≈-refl tt
    canonical-principal {A = A} (⇒-conv {T = B} der eq) cv
      with canonical-principal der cv
    ... | principal P h rigid between shape =
      principal P h rigid (≈-trans {t = P} {u = B} {v = A} between eq) shape
    canonical-principal (⇒-cumul der le) cv =
      principal _ _ ty-universe ≈-refl tt

    canonical-principal⇐ : ∀ {n} {Γ : Ctx n} {v A}
      → Γ ⊢ v ⇐ A → Canonical v → Principal v A
    canonical-principal⇐ (⇐-lam {g = g} {d = d} {b = b} p q) c-lam =
      principal _ _ ty-pi ≈-refl (g , d , b , refl)
    canonical-principal⇐ ⇐-hole ()
    canonical-principal⇐ {A = A} (⇐-infer {T′ = B} der eq) cv
      with canonical-principal der cv
    ... | principal P h rigid between shape =
      principal P h rigid (≈-trans {t = P} {u = B} {v = A} between eq) shape
    canonical-principal⇐ {A = A} (⇐-conv {T = B} der eq) cv
      with canonical-principal⇐ der cv
    ... | principal P h rigid between shape =
      principal P h rigid (≈-trans {t = P} {u = B} {v = A} between eq) shape
    canonical-principal⇐ (⇐-cumul der le) cv =
      principal _ _ ty-universe ≈-refl tt

    canonical-at : ∀ {n} {Γ : Ctx n} {v A h}
      → Γ ⊢ v ⇒ A → Canonical v → HasTypeHead A h → Shape h v
    canonical-at {v = v} {A = A} der cv target with canonical-principal der cv
    ... | principal P h rigid equal shape =
      subst (λ head → Shape head v)
        (≈-heads {t = P} {u = A} rigid target equal) shape

    canonical-pi : ∀ {n} {Γ : Ctx n} {v g d c}
      → Γ ⊢ v ⇒ tm-pi g d c → Canonical v → Lambda v
    canonical-pi der cv = canonical-at der cv ty-pi

    canonical-data : ∀ {n} {Γ : Ctx n} {v name ps is}
      → Γ ⊢ v ⇒ tm-data name ps is → Canonical v → ConstructorLike v
    canonical-data der cv = canonical-at der cv ty-data

    canonical-at⇐ : ∀ {n} {Γ : Ctx n} {v A h}
      → Γ ⊢ v ⇐ A → Canonical v → HasTypeHead A h → Shape h v
    canonical-at⇐ {v = v} {A = A} der cv target with canonical-principal⇐ der cv
    ... | principal P h rigid equal shape =
      subst (λ head → Shape head v)
        (≈-heads {t = P} {u = A} rigid target equal) shape

    canonical-pi⇐ : ∀ {n} {Γ : Ctx n} {v g d c}
      → Γ ⊢ v ⇐ tm-pi g d c → Canonical v → Lambda v
    canonical-pi⇐ der cv = canonical-at⇐ der cv ty-pi

    canonical-data⇐ : ∀ {n} {Γ : Ctx n} {v name ps is}
      → Γ ⊢ v ⇐ tm-data name ps is → Canonical v → ConstructorLike v
    canonical-data⇐ der cv = canonical-at⇐ der cv ty-data

    nat-source : ∀ {n} {Γ : Ctx n} {k A}
      → Γ ⊢ tm-nat_lit k ⇒ A
      → ∃ λ name → IndEnv.builtins ind "nat" ≡ just name
        × (tm-data name [] [] ≈ A)
    nat-source (⇒-nat_lit {name = name} builtin found pars indices) =
      name , builtin , ≈-refl
    nat-source {A = A} (⇒-conv {T = B} der eq) with nat-source der
    ... | name , builtin , between = name , builtin ,
      ≈-trans {t = tm-data name [] []} {u = B} {v = A} between eq
    nat-source (⇒-cumul der le) with nat-source der
    ... | name , builtin , between = ⊥-elim (data-not-sort between)

    bounded-source : ∀ {n} {Γ : Ctx n} {k A}
      → Γ ⊢ tm-bounded_lit k ⇒ A
      → ∃ λ name → IndEnv.builtins ind "bounded" ≡ just name
        × (tm-data name [] [] ≈ A)
    bounded-source (⇒-bounded_lit {name = name} builtin found pars indices) =
      name , builtin , ≈-refl
    bounded-source {A = A} (⇒-conv {T = B} der eq) with bounded-source der
    ... | name , builtin , between = name , builtin ,
      ≈-trans {t = tm-data name [] []} {u = B} {v = A} between eq
    bounded-source (⇒-cumul der le) with bounded-source der
    ... | name , builtin , between = ⊥-elim (data-not-sort between)

    data-name : ∀ {a ps is b qs js}
      → tm-data a ps is ≈ tm-data b qs js → a ≡ b
    data-name {a} {ps} {is} {b} {qs} {js} equal =
      data-head-injective
        (≈-heads {t = tm-data a ps is} {u = tm-data b qs js} ty-data ty-data equal)

    nat-lit-family : ∀ {n} {Γ : Ctx n} {k name ps is}
      → Γ ⊢ tm-nat_lit k ⇒ tm-data name ps is
      → IndEnv.builtins ind "nat" ≡ just name
    nat-lit-family der with nat-source der
    ... | name , builtin , between =
      subst (λ n → IndEnv.builtins ind "nat" ≡ just n) (data-name between) builtin

    bounded-lit-family : ∀ {n} {Γ : Ctx n} {k name ps is}
      → Γ ⊢ tm-bounded_lit k ⇒ tm-data name ps is
      → IndEnv.builtins ind "bounded" ≡ just name
    bounded-lit-family der with bounded-source der
    ... | name , builtin , between =
      subst (λ n → IndEnv.builtins ind "bounded" ≡ just n) (data-name between) builtin
