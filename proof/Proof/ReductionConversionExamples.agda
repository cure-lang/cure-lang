------------------------------------------------------------------------
-- Full reduction compatibility is POSITIVE evidence here, unlike the
-- earlier zeta-only record witness. Negative controls reject value
-- collapse, universe/grade/family confusion, and unsupported eta.
------------------------------------------------------------------------
module Proof.ReductionConversionExamples where

open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Core.Grade using (unrestricted; erased)
open import Core.Universe using (l0; l1)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Reduction
open import Core.Typing using (Conversion; Ctx; ⟨⟩; extend)
open import Core.LiteralExpansion
import Proof.ReductionConversion as Reduction
import Proof.LiteralCases as L
import Proof.CoverageExamples as Cases

module R = Reduction.Model L.empty-sig
  (λ {f} {b} p → L.empty-closed {f} {b} p)

pi-type let-pi : Term
pi-type = tm-pi unrestricted tm-int_type tm-int_type
let-pi = tm-let unrestricted (tm-type l0) pi-type (tm-var 0)

let-converts : R._≈_ let-pi pi-type
let-converts = R.reduce-converts {t = let-pi} {u = pi-type} ζ

beta-converts : R._≈_
  (tm-app (tm-lam unrestricted tm-int_type (tm-var 0)) (tm-int_lit (pos 7)))
  (tm-int_lit (pos 7))
beta-converts = R.reduce-converts
  {t = tm-app (tm-lam unrestricted tm-int_type (tm-var 0)) (tm-int_lit (pos 7))}
  {u = tm-int_lit (pos 7)} β

z-peel : R._≈_ L.z-case L.result
z-peel = R.reduce-converts L.z-contracts
s-peel : R._≈_ L.s-case (tm-nat_lit 7)
s-peel = R.reduce-converts L.s-contracts
first-peel : R._≈_ L.first-case L.result
first-peel = R.reduce-converts L.first-contracts
next-peel : R._≈_ L.next-case L.result
next-peel = R.reduce-converts L.next-contracts

compact-zero : R._≈_ (tm-ctor "Z" []) (tm-nat_lit 0)
compact-zero = Conversion.≈-nat-zero R.conversion
compact-successor : R._≈_ (tm-ctor "S" (tm-nat_lit 7 ∷ [])) (tm-nat_lit 8)
compact-successor = Conversion.≈-nat-suc R.conversion {k = 7}
compact-first : R._≈_ (tm-ctor "First" (tm-nat_lit 0 ∷ [])) (tm-bounded_lit 0)
compact-first = Conversion.≈-bounded-zero R.conversion
compact-next : R._≈_ (tm-ctor "Next" (tm-nat_lit 7 ∷ tm-bounded_lit 7 ∷ [])) (tm-bounded_lit 8)
compact-next = Conversion.≈-bounded-suc R.conversion {k = 7}

nat-normal : ∀ n → R.C.NormalForm (nat n)
nat-normal zero (ξ-ctor-at () p)
nat-normal (suc n) (ξ-ctor-at Fin.zero p) = nat-normal n p
nat-normal (suc n) (ξ-ctor-at (Fin.suc ()) p)

bounded-normal : ∀ n → R.C.NormalForm (bounded n)
bounded-normal zero (ξ-ctor-at Fin.zero p) = nat-normal 0 p
bounded-normal zero (ξ-ctor-at (Fin.suc ()) p)
bounded-normal (suc n) (ξ-ctor-at Fin.zero p) = nat-normal n p
bounded-normal (suc n) (ξ-ctor-at (Fin.suc Fin.zero) p) = bounded-normal n p
bounded-normal (suc n) (ξ-ctor-at (Fin.suc (Fin.suc ())) p)

normal-join-equal : ∀ {t u} → R.C.NormalForm t → R.C.NormalForm u → R._~_ t u → t ≡ u
normal-join-equal nt nu (w , p , q) =
  trans (R.C.normal-path nt p) (sym (R.C.normal-path nu q))

zero-not-one : nat 0 ≡ nat 1 → ⊥
zero-not-one ()
different-nats : R._≈_ (tm-nat_lit 0) (tm-nat_lit 1) → ⊥
different-nats eq = zero-not-one (normal-join-equal (nat-normal 0) (nat-normal 1) eq)

first-not-next : bounded 0 ≡ bounded 1 → ⊥
first-not-next ()
different-bounded : R._≈_ (tm-bounded_lit 0) (tm-bounded_lit 1) → ⊥
different-bounded eq = first-not-next (normal-join-equal (bounded-normal 0) (bounded-normal 1) eq)

int-normal : ∀ k → R.C.NormalForm (tm-int_lit k)
int-normal k ()
int-values-distinct : tm-int_lit (pos 7) ≡ tm-int_lit (pos 9) → ⊥
int-values-distinct ()
different-ints : R._≈_ (tm-int_lit (pos 7)) (tm-int_lit (pos 9)) → ⊥
different-ints eq = int-values-distinct (normal-join-equal (int-normal _) (int-normal _) eq)

universe-distinct : R._≈_ (tm-type l0) (tm-type l1) → ⊥
universe-distinct eq with R.model-heads ty-universe ty-universe eq
... | ()
family-distinct : R._≈_ (tm-data "Nat" [] []) (tm-data "Bool" [] []) → ⊥
family-distinct eq with R.model-heads ty-data ty-data eq
... | ()
grade-distinct : R._≈_ (tm-pi erased tm-int_type tm-int_type) pi-type → ⊥
grade-distinct eq with proj₁ (Conversion.≈-pi-components R.conversion
  {g = unrestricted} {d = tm-int_type} {c = tm-int_type}
  {g′ = erased} {d′ = tm-int_type} {c′ = tm-int_type} eq)
... | ()

hole-normal : ∀ n → R.C.NormalForm (tm-hole n)
hole-normal n ()
hole-names-distinct : tm-hole "left" ≡ tm-hole "right" → ⊥
hole-names-distinct ()
different-holes : R._≈_ (tm-hole "left") (tm-hole "right") → ⊥
different-holes eq = hole-names-distinct (normal-join-equal (hole-normal _) (hole-normal _) eq)

-- Open neutral eta: both expanded terms are distinct normal forms.
eta-function : Term
eta-function = tm-lam unrestricted tm-int_type (tm-app (tm-var 1) (tm-var 0))

eta-normal : R.C.NormalForm eta-function
eta-normal (ξ-lam-dom ())
eta-normal (ξ-lam-body (ξ-app₁ ()))
eta-normal (ξ-lam-body (ξ-app₂ ()))

variable-normal : R.C.NormalForm (tm-var 0)
variable-normal ()
lambda-not-variable : eta-function ≡ tm-var 0 → ⊥
lambda-not-variable ()
eta-not-in-this-model : R._≈_ eta-function (tm-var 0) → ⊥
eta-not-in-this-model eq = lambda-not-variable (normal-join-equal eta-normal variable-normal eq)

module TypedEta where
  open Core.Typing.Typing Cases.env L.empty-sig R.conversion
  Γ : Ctx 1
  Γ = extend ⟨⟩ pi-type

  neutral-typed : Γ ⊢ tm-var 0 ⇒ pi-type
  neutral-typed = ⇒-var Fin.zero

  eta-function-typed : Γ ⊢ eta-function ⇒ pi-type
  eta-function-typed = ⇒-lam ⇒-int_type
    (⇐-infer (⇒-app (⇒-var (Fin.suc Fin.zero)) (⇒-var Fin.zero))
      (Conversion.≈-refl R.conversion {t = tm-int_type}))
