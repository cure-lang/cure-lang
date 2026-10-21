------------------------------------------------------------------------
-- Compositional closures with actual local steps and native endpoints.
-- These examples do NOT assert a recursive preservation theorem.
------------------------------------------------------------------------
module Proof.DependentCongruenceExamples where

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Signature using (ctor-indices)
open import Core.Reduction
open import Core.Typing using (⟨⟩; extend; Conversion)
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentCongruence as Congruence

open E.T
open Conversion
module C = Congruence.Laws E.env E.sig E.conv E.valid
  (λ {t} {u} → E.R.reduce-converts {t} {u})

float-computation atom-computation : Term
float-computation = tm-let unrestricted tm-atom_type (tm-atom_lit "payload") tm-float_type
atom-computation = tm-let unrestricted tm-atom_type (tm-atom_lit "payload") tm-atom_type

source-fields : Data.List.List Term
source-fields = tm-atom_lit "payload" ∷ float-computation ∷ tm-float_lit ∷ []

source-goal wrapped-goal : Term
source-goal = tm-data "NativeD" (tm-atom_type ∷ []) source-fields
wrapped-goal = tm-let unrestricted (tm-type l0) source-goal (tm-var 0)

abstract
  float-computation-kind : ⟨⟩ ⊢ float-computation ⇒ tm-type l0
  float-computation-kind = ⇒-let ⇒-atom_type (E.check ⇒-atom_lit) ⇒-float_type

  float-converts : _≈_ E.conv tm-float_type float-computation
  float-converts = ≈-sym E.conv {t = float-computation} {u = tm-float_type}
    (E.R.reduce-converts {t = float-computation} {u = tm-float_type} ζ)

  source-result-conversion : _≈_ E.conv source-goal wrapped-goal
  source-result-conversion = ≈-sym E.conv {t = wrapped-goal} {u = source-goal}
    (E.R.reduce-converts {t = wrapped-goal} {u = source-goal} ζ)

-- Transparent spine/record witnesses let expected-at compute the selected
-- native declaration's expected type without unfolding the model.
source-spine : Spine ⟨⟩ (tm-atom_type ∷ []) source-fields E.indices
source-spine = sp∷ (E.check ⇒-atom_lit)
  (sp∷ (E.check float-computation-kind)
    (sp∷ (⇐-infer {T′ = tm-float_type} ⇒-float_lit float-converts) sp[]))

source-view : C.I.ConstructorView ⟨⟩ "NativeComputed" source-fields
  (tm-let unrestricted (tm-type l0)
    (tm-data "NativeD" (tm-atom_type ∷ [])
      (F.instantiateResults (tm-atom_type ∷ []) source-fields (ctor-indices E.computed)))
    (tm-var 0))
source-view = record
  { family = E.family ; ctor = E.computed ; parameters = tm-atom_type ∷ []
  ; found = refl ; parameters-checked = E.actual-parameters ; fields-checked = source-spine
  ; result-conversion =
      ≈-sym E.conv
        {t = tm-let unrestricted (tm-type l0)
          (tm-data "NativeD" (tm-atom_type ∷ [])
            (F.instantiateResults (tm-atom_type ∷ []) source-fields (ctor-indices E.computed)))
          (tm-var 0)}
        {u = tm-data "NativeD" (tm-atom_type ∷ [])
          (F.instantiateResults (tm-atom_type ∷ []) source-fields (ctor-indices E.computed))}
        (E.R.reduce-converts
          {t = tm-let unrestricted (tm-type l0)
            (tm-data "NativeD" (tm-atom_type ∷ [])
              (F.instantiateResults (tm-atom_type ∷ []) source-fields (ctor-indices E.computed)))
            (tm-var 0)}
          {u = tm-data "NativeD" (tm-atom_type ∷ [])
            (F.instantiateResults (tm-atom_type ∷ []) source-fields (ctor-indices E.computed))}
          ζ) }

abstract
  non-head-constructor :
    ⟨⟩ ⊢ tm-ctor "NativeComputed" E.fields ⇒
      tm-let unrestricted (tm-type l0)
        (tm-data "NativeD" (tm-atom_type ∷ [])
          (F.instantiateResults (tm-atom_type ∷ []) source-fields (ctor-indices E.computed)))
        (tm-var 0)
  non-head-constructor = C.ctor-at source-view (suc zero) ζ (E.check ⇒-float_type)

  non-head-constructor-step : _⇝_ E.sig
    (tm-ctor "NativeComputed" source-fields) (tm-ctor "NativeComputed" E.fields)
  non-head-constructor-step = ξ-ctor-at (suc zero) ζ

  non-head-data : ⟨⟩ ⊢ E.goal ⇒ tm-type Core.Universe.l1
  non-head-data = C.data-indices-at {name = "NativeD"} refl
    E.actual-parameters source-spine (suc zero) ζ (E.check ⇒-float_type)

  binder-domain : ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-var 0)
    ⇒ tm-pi unrestricted atom-computation atom-computation
  binder-domain = C.lam-dom wf[] ζ
    (⇒-let ⇒-atom_type (E.check ⇒-atom_lit) ⇒-atom_type)
    ⇒-atom_type (E.check (⇒-var zero))

  binder-domain-step : _⇝_ E.sig
    (tm-lam unrestricted atom-computation (tm-var 0))
    (tm-lam unrestricted tm-atom_type (tm-var 0))
  binder-domain-step = ξ-lam-dom ζ

  nested-case-source : extend ⟨⟩ tm-atom_type ⊢ E.program ⇒ tm-float_type
  nested-case-source = C.GV.rename⇒ (C.G.C.weakening ⟨⟩ tm-atom_type)
    (wf∷ wf[] sc-atom_type ⇒-atom_type) E.program-typed

  nested-case-body : ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type tm-float_lit
    ⇒ tm-pi unrestricted tm-atom_type tm-float_type
  nested-case-body = C.lam-body (ι refl refl) ⇒-atom_type
    (E.check nested-case-source) (E.check ⇒-float_lit)

  nested-case-step : _⇝_ E.sig
    (tm-lam unrestricted tm-atom_type E.program)
    (tm-lam unrestricted tm-atom_type tm-float_lit)
  nested-case-step = ξ-lam-body (ι refl refl)
