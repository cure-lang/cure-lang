{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Bounded registered constructor preservation, not unified Core soundness.
-- Reducing B changes y's raw expected type in (x : A, B : Type0, y : B).
------------------------------------------------------------------------
module Proof.DependentPreservationExamples where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Reduction
open import Core.Signature using (ctor-args; just-inj)
open import Core.TypeHeads using (ty-data)
open import Core.Typing using (⟨⟩; Conversion)
open import Proof.Progress
  using (Final; ft[]; ft∷; f-app; f-lam; f-type; f-var; f-atom_type; f-atom_lit; f-float_type; f-float_lit)
import Proof.SoundnessModel as M
import Proof.DependentRegistryExamples as G
import Proof.DependentResultExamples as X
import Proof.DependentInstantiationExamples as E
import Proof.DependentSpineExamples as Earlier
import Proof.DependentPreservation as Preservation

open Core.Typing.Typing M.env M.sig M.conv
module Q = Preservation.Preserve M.env M.sig M.conv G.registry
  M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final
open G.L.T using (as[]; as∷)

type-redex : Term
type-redex = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-float_type
type-redex-typed : ⟨⟩ ⊢ type-redex ⇒ tm-type l0
type-redex-typed = ⇒-app
  (⇒-lam {c = tm-type l0} (⇒-type refl)
    (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-type l0}))) ⇒-float_type
type-redex-final : Final type-redex
type-redex-final = f-app (f-lam f-type f-var) f-float_type
type-converts : Conversion._≈_ M.conv type-redex tm-float_type
type-converts = M.rc {t = type-redex} {t′ = tm-float_type} β

source-fields target-fields : List Term
source-fields = tm-atom_lit "payload" ∷ type-redex ∷ tm-float_lit ∷ []
target-fields = tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []
goal target-result : Term
goal = tm-data "LocalResult" (tm-atom_type ∷ []) source-fields
target-result = tm-data "LocalResult" (tm-atom_type ∷ []) target-fields

source-arguments :
  G.L.T.Arguments ⟨⟩ (tm-atom_type ∷ []) source-fields (ctor-args X.ctor)
source-arguments =
  as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type}))
    (as∷ (⇐-infer type-redex-typed (M.eq-refl {tm-type l0}))
      (as∷ (⇐-infer ⇒-float_lit
        (Conversion.≈-sym M.conv {t = type-redex} {u = tm-float_type} type-converts)) as[]))

source : G.L.Application ⟨⟩ "LocalMk" (tm-atom_type ∷ []) source-fields
source = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.ctor ; found = refl
  ; parameters = E.parameter-arguments ; fields = source-arguments
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ type-redex-final (ft∷ f-float_lit ft[])) }
checked-source : Q.CheckedApplication ⟨⟩ "LocalMk" (tm-atom_type ∷ []) source-fields goal
checked-source = record { application = source ; at-goal = M.eq-refl {goal} }

middle-step : _⇝_ M.sig (tm-ctor "LocalMk" source-fields) (tm-ctor "LocalMk" target-fields)
middle-step = ξ-ctor-at (Fin.suc Fin.zero) β
preserved : Q.CheckedApplication ⟨⟩ "LocalMk" (tm-atom_type ∷ []) target-fields goal
preserved = Q.preserve-at checked-source (Fin.suc Fin.zero) β
preserved-step :
  Σ (List Term) (λ args → tm-ctor "LocalMk" target-fields ≡ tm-ctor "LocalMk" args
    × Q.CheckedApplication ⟨⟩ "LocalMk" (tm-atom_type ∷ []) args goal)
preserved-step = Q.preserve-step checked-source middle-step
target-formation : G.L.Formation ⟨⟩ "LocalResult" (tm-atom_type ∷ []) target-fields
target-formation = G.A.result-formation (Q.application preserved)

-- The raw result has CHANGED; preservation must keep the old goal by
-- conversion, not quietly replace it by the new inferred result.
raw-results-differ : goal ≡ target-result → ⊥
raw-results-differ ()
fixed-goal-conversion : Conversion._≈_ M.conv target-result goal
fixed-goal-conversion = Q.at-goal preserved

computed-source : G.L.Application ⟨⟩ "LocalComputed" (tm-atom_type ∷ []) source-fields
computed-source = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.computed-ctor ; found = refl
  ; parameters = E.parameter-arguments ; fields = source-arguments
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ type-redex-final (ft∷ f-float_lit ft[])) }
computed-goal : Term
computed-goal = tm-data "LocalResult" (tm-atom_type ∷ [])
  (X.computed-result ∷ type-redex ∷ tm-float_lit ∷ [])
computed-checked : Q.CheckedApplication ⟨⟩ "LocalComputed" (tm-atom_type ∷ []) source-fields computed-goal
computed-checked = record { application = computed-source ; at-goal = M.eq-refl {computed-goal} }
computed-preserved :
  Q.CheckedApplication ⟨⟩ "LocalComputed" (tm-atom_type ∷ []) target-fields computed-goal
computed-preserved = Q.preserve-at computed-checked (Fin.suc Fin.zero) β

-- Two actual constructor steps: first the type-valued B field, then y.
value-redex : Term
value-redex = tm-app (tm-lam unrestricted tm-float_type (tm-var 0)) tm-float_lit
value-redex-typed : ⟨⟩ ⊢ value-redex ⇒ tm-float_type
value-redex-typed = ⇒-app
  (⇒-lam {c = tm-float_type} ⇒-float_type
    (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-float_type}))) ⇒-float_lit
value-redex-final : Final value-redex
value-redex-final = f-app (f-lam f-float_type f-var) f-float_lit
two-fields : List Term
two-fields = tm-atom_lit "payload" ∷ type-redex ∷ value-redex ∷ []
two-goal : Term
two-goal = tm-data "LocalResult" (tm-atom_type ∷ []) two-fields
two-source : G.L.Application ⟨⟩ "LocalMk" (tm-atom_type ∷ []) two-fields
two-source = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.ctor ; found = refl
  ; parameters = E.parameter-arguments
  ; fields = as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type}))
      (as∷ (⇐-infer type-redex-typed (M.eq-refl {tm-type l0}))
        (as∷ (⇐-infer value-redex-typed
          (Conversion.≈-sym M.conv {t = type-redex} {u = tm-float_type} type-converts)) as[]))
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ type-redex-final (ft∷ value-redex-final ft[])) }
two-checked : Q.CheckedApplication ⟨⟩ "LocalMk" (tm-atom_type ∷ []) two-fields two-goal
two-checked = record { application = two-source ; at-goal = M.eq-refl {two-goal} }
two-path : _⇝*_ M.sig (tm-ctor "LocalMk" two-fields) (tm-ctor "LocalMk" target-fields)
two-path = ⇝*-step (ξ-ctor-at (Fin.suc Fin.zero) β)
  (⇝*-step (ξ-ctor-at (Fin.suc (Fin.suc Fin.zero)) β) ⇝*-refl)
two-preserved :
  Σ (List Term) (λ args → tm-ctor "LocalMk" target-fields ≡ tm-ctor "LocalMk" args
    × Q.CheckedApplication ⟨⟩ "LocalMk" (tm-atom_type ∷ []) args two-goal)
two-preserved = Q.preserve-star two-checked two-path

-- Open callers exercise the same conversion without capturing their x.
open-source : G.L.Application E.Γ "LocalMk" (tm-atom_type ∷ [])
  (tm-var 0 ∷ type-redex ∷ tm-float_lit ∷ [])
open-source = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.ctor ; found = refl
  ; parameters = E.open-parameters
  ; fields = as∷ (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-atom_type}))
      (as∷ (⇐-infer type-redex-typed-open (M.eq-refl {tm-type l0}))
        (as∷ (⇐-infer ⇒-float_lit
          (Conversion.≈-sym M.conv {t = type-redex} {u = tm-float_type} type-converts)) as[]))
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-var (ft∷ type-redex-final (ft∷ f-float_lit ft[])) }
  where
    type-redex-typed-open : E.Γ ⊢ type-redex ⇒ tm-type l0
    type-redex-typed-open = ⇒-app
      (⇒-lam {c = tm-type l0} (⇒-type refl)
        (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-type l0}))) ⇒-float_type
open-goal : Term
open-goal = tm-data "LocalResult" (tm-atom_type ∷ []) (tm-var 0 ∷ type-redex ∷ tm-float_lit ∷ [])
open-checked : Q.CheckedApplication E.Γ "LocalMk" (tm-atom_type ∷ [])
  (tm-var 0 ∷ type-redex ∷ tm-float_lit ∷ []) open-goal
open-checked = record { application = open-source ; at-goal = M.eq-refl {open-goal} }
open-preserved : Q.CheckedApplication E.Γ "LocalMk" (tm-atom_type ∷ [])
  (tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ []) open-goal
open-preserved = Q.preserve-at open-checked (Fin.suc Fin.zero) β

bad-nonconvertible-update :
  G.L.Application ⟨⟩ "LocalMk" (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ []) → ⊥
bad-nonconvertible-update app with just-inj (G.L.Application.found app)
... | refl with G.L.Application.fields app
... | as∷ first (as∷ second (as∷ bad rest)) =
  Earlier.float-at-atom (M.P.check-infer (λ name ()) bad) (M.eq-refl {tm-atom_type})
wrong-result-family : Conversion._≈_ M.conv target-result M.N → ⊥
wrong-result-family equal
  with Conversion.≈-heads M.conv {t = target-result} {u = M.N} ty-data ty-data equal
... | ()
