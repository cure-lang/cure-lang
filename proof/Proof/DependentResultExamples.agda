{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- LOCAL declaration evidence, not active dependent global admission.
-- Indices depend on parameters AND preceding indices, with distinct types.
------------------------------------------------------------------------
module Proof.DependentResultExamples where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l≤-refl; l0≤l1)
open import Core.Syntax
open import Core.Signature
  using (Family; Ctor; fam-indices; ctor-indices; ctor-params)
open import Core.Reduction using (β)
open import Core.Typing using (Ctx; ⟨⟩; extend; _∈Tele_; ∈-here)
open import Proof.Progress
  using (ft[]; ft∷; f-atom_type; f-atom_lit; f-float_type; f-float_lit; f-var)
import Core.LocalFrame as F
import Proof.DependentResult as Result
import Proof.DependentInstantiationExamples as E
import Proof.DependentSpineExamples as Earlier
import Proof.SoundnessModel as M

open Core.Typing.Typing M.env M.sig M.conv
module R = Result.Results M.env M.sig M.conv
module K = R.Transport M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final
open R.T using (dt[]; dt∷; as[]; as∷)
open R.D using (ds[]; ds∷)

-- D(A : Type0; x : A, B : Type0, y : B).
-- The field and index telescopes have the same shape, so their final
-- local contexts coincide: [y : B, B : Type0, x : A, A : Type0].
family : Family
family = record
  { fam-name = "LocalResult" ; fam-params = E.parameters
  ; fam-indices = ("x" , tm-var 0) ∷ ("B" , tm-type l0) ∷ ("y" , tm-var 0) ∷ []
  ; fam-level = l1 ; fam-ctors = [] ; positive = true ; universe-ok = true }
ctor : Ctor
ctor = record
  { ctor-name = "LocalMk" ; ctor-args = fam-indices family
  ; ctor-params = tm-var 3 ∷ []
  ; ctor-indices = tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ [] }

Ξ : Ctx 3
Ξ = extend E.Φ (tm-type l0)
Φ : Ctx 4
Φ = extend Ξ (tm-var 0)

fields-declared : R.T.Declared E.Π (fam-indices family) Φ
fields-declared =
  dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero)
    (dt∷ sc-type (⇒-type refl)
      (dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[]))

local-results : R.ResultSpines Φ family (ctor-params ctor) (ctor-indices ctor)
local-results = record
  { parameters-checked = ds∷ sc-type (⇒-type refl)
      (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) (M.eq-refl {tm-type l0})) ds[]
  ; indices-checked =
      ds∷ (sc-var (s≤s z≤n)) (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
        (⇐-infer (⇒-var (Fin.suc (Fin.suc Fin.zero))) (M.eq-refl {tm-var 3}))
        (ds∷ sc-type (⇒-type refl)
          (⇐-infer (⇒-var (Fin.suc Fin.zero)) (M.eq-refl {tm-type l0}))
          (ds∷ (sc-var (s≤s z≤n)) (⇒-var (Fin.suc Fin.zero))
            (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-var 1})) ds[])) }

declaration : R.LocalDeclaration family ctor E.Π Φ Φ
declaration = record
  { parameter-declarations = E.parameter-declarations
  ; index-declarations = fields-declared ; field-declarations = fields-declared
  ; field-levels = l0≤l1 , l≤-refl , l0≤l1 , tt
  ; result-scoping = st∷ (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) st[] ,
      st∷ (sc-var (s≤s (s≤s (s≤s z≤n))))
        (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[]))
  ; uniform-parameters = refl ; result-spines = local-results }

actual-fields :
  R.T.Arguments ⟨⟩ (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) (fam-indices family)
actual-fields =
  as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type}))
    (as∷ (⇐-infer ⇒-float_type (M.eq-refl {tm-type l0}))
      (as∷ (⇐-infer ⇒-float_lit (M.eq-refl {tm-float_type})) as[]))

instantiated-results :
  R.ResultSpines ⟨⟩ family (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
instantiated-results = K.instantiate-results declaration E.parameter-arguments actual-fields
  (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[])))

computed-x : Term
computed-x = tm-app (tm-lam unrestricted (tm-var 3) (tm-var 0)) (tm-var 2)
computed-x-typed : Φ ⊢ computed-x ⇒ tm-var 3
computed-x-typed = ⇒-app
  (⇒-lam {c = tm-var 4} (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
    (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-var 4})))
  (⇒-var (Fin.suc (Fin.suc Fin.zero)))
computed-ctor : Ctor
computed-ctor = record ctor
  { ctor-name = "LocalComputed" ; ctor-indices = computed-x ∷ tm-var 1 ∷ tm-var 0 ∷ [] }
computed-declaration : R.LocalDeclaration family computed-ctor E.Π Φ Φ
computed-declaration = record
  { parameter-declarations = E.parameter-declarations
  ; index-declarations = fields-declared ; field-declarations = fields-declared
  ; field-levels = l0≤l1 , l≤-refl , l0≤l1 , tt
  ; uniform-parameters = refl
  ; result-scoping = st∷ (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) st[] ,
      st∷ (sc-app (sc-lam (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) (sc-var (s≤s z≤n)))
        (sc-var (s≤s (s≤s (s≤s z≤n)))))
        (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[]))
  ; result-spines = record
      { parameters-checked = R.parameters-checked local-results
      ; indices-checked =
          ds∷ (sc-var (s≤s z≤n)) (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
            (⇐-infer computed-x-typed (M.eq-refl {tm-var 3}))
            (ds∷ sc-type (⇒-type refl)
              (⇐-infer (⇒-var (Fin.suc Fin.zero)) (M.eq-refl {tm-type l0}))
              (ds∷ (sc-var (s≤s z≤n)) (⇒-var (Fin.suc Fin.zero))
                (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-var 1})) ds[])) } }
computed-result : Term
computed-result = tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) (tm-atom_lit "payload")
computed-results :
  R.ResultSpines ⟨⟩ family (tm-atom_type ∷ [])
    (computed-result ∷ tm-float_type ∷ tm-float_lit ∷ [])
computed-results = K.instantiate-results computed-declaration E.parameter-arguments actual-fields
  (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[])))
computed-component-converts :
  Core.Typing.Conversion._≈_ M.conv computed-result (tm-atom_lit "payload")
computed-component-converts = M.rc {t = computed-result} {t′ = tm-atom_lit "payload"} β

parameters-restored :
  F.instantiateResults (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) (ctor-params ctor)
    ≡ tm-atom_type ∷ []
parameters-restored = K.uniform-instantiates family ctor (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) refl refl refl

-- A caller variable is not captured by the constructor's declaration frame.
open-fields :
  R.T.Arguments E.Γ (tm-atom_type ∷ [])
    (tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ []) (fam-indices family)
open-fields =
  as∷ (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-atom_type}))
    (as∷ (⇐-infer ⇒-float_type (M.eq-refl {tm-type l0}))
      (as∷ (⇐-infer ⇒-float_lit (M.eq-refl {tm-float_type})) as[]))
open-results :
  R.ResultSpines E.Γ family (tm-atom_type ∷ [])
    (tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ [])
open-results = K.instantiate-results declaration E.open-parameters open-fields
  (ft∷ f-atom_type ft[]) (ft∷ f-var (ft∷ f-float_type (ft∷ f-float_lit ft[])))

bad-later-index-rejected :
  R.ResultSpines ⟨⟩ family (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ []) → ⊥
bad-later-index-rejected checked with R.indices-checked checked
... | ds∷ scope kind first (ds∷ scope′ kind′ second (ds∷ scope″ kind″ bad rest)) =
  Earlier.float-at-atom (M.P.check-infer (λ name ()) bad) (M.eq-refl {tm-atom_type})
bad-parameter-result-rejected :
  R.ResultSpines ⟨⟩ family (tm-float_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) → ⊥
bad-parameter-result-rejected checked with R.indices-checked checked
... | ds∷ scope kind bad rest =
  E.atom-at-float (M.P.check-infer (λ name ()) bad) (M.eq-refl {tm-float_type})
missing-indices-rejected : R.ResultSpines ⟨⟩ family (tm-atom_type ∷ []) [] → ⊥
missing-indices-rejected checked with R.indices-checked checked
... | ()
surplus-indices-rejected :
  R.ResultSpines ⟨⟩ family (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ tm-float_lit ∷ []) → ⊥
surplus-indices-rejected checked with R.result-arities checked
... | parameters-size , ()

-- A universe budget is a REAL premise of this specific declaration
-- witness: the Type0 field has sort Type1 and cannot fit in family Type0.
too-small-field-budget : R.LevelsBelow l0 fields-declared → ⊥
too-small-field-budget (first , () , rest)

-- Both result parameters are well-typed, but swapping them is NON-uniform.
dual-family : Family
dual-family = record
  { fam-name = "LocalDual" ; fam-params = E.parameters₂ ; fam-indices = []
  ; fam-level = l1 ; fam-ctors = [] ; positive = true ; universe-ok = true }
nonuniform-ctor : Ctor
nonuniform-ctor = record
  { ctor-name = "LocalSwap" ; ctor-args = E.fields₂
  ; ctor-params = tm-var 2 ∷ tm-var 3 ∷ [] ; ctor-indices = [] }
nonuniform-still-typed :
  R.ResultSpines E.Φ₂ dual-family (ctor-params nonuniform-ctor) []
nonuniform-still-typed = record
  { parameters-checked =
      ds∷ sc-type (⇒-type refl)
        (⇐-infer (⇒-var (Fin.suc (Fin.suc Fin.zero))) (M.eq-refl {tm-type l0}))
        (ds∷ sc-type (⇒-type refl)
          (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) (M.eq-refl {tm-type l0})) ds[])
  ; indices-checked = ds[] }
nonuniform-rejected : Result.UniformParameters dual-family nonuniform-ctor → ⊥
nonuniform-rejected ()
nonuniform-declaration-rejected :
  R.LocalDeclaration dual-family nonuniform-ctor E.Π₂ E.Π₂ E.Φ₂ → ⊥
nonuniform-declaration-rejected candidate = nonuniform-rejected (R.uniform-parameters candidate)

-- The active data-formation adapter really works for a registered CLOSED
-- family; the genuinely dependent family above fails its closedness gate.
closed-results : R.ResultSpines ⟨⟩ M.bounded-family [] []
closed-results = record { parameters-checked = ds[] ; indices-checked = ds[] }
active-closed-result-kind : ⟨⟩ ⊢ M.B ⇒ tm-type l0
active-closed-result-kind = K.active-result-kind refl (λ ()) (λ ()) closed-results
dependent-indices-not-closed :
  (∀ {A} → A ∈Tele fam-indices family → Scoped 0 A) → ⊥
dependent-indices-not-closed closed with closed ∈-here
... | sc-var ()
