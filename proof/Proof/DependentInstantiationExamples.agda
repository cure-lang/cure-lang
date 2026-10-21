{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Genuine local dependent declaration/instantiation witnesses.
-- No dependent constructor is registered through the closed-entry rules.
------------------------------------------------------------------------
module Proof.DependentInstantiationExamples where

open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l2)
open import Core.Syntax
open import Core.Signature using (Telescope)
open import Core.Reduction using (β)
open import Core.Typing using (Ctx; Conversion; ⟨⟩; extend)
open import Core.TypeHeads using (ty-atom; ty-float; ty-universe)
open import Proof.Progress using (Final; FinalTerms; ft[]; ft∷; f-atom_type; f-atom_lit; f-float_type; f-float_lit; f-var; f-app; f-lam; f-type)
import Core.LocalFrame as F
import Proof.SoundnessModel as M
import Proof.DependentInstantiation as Instantiation
import Proof.DependentSpineExamples as Earlier

open Core.Typing.Typing M.env M.sig M.conv
module T = Instantiation.Telescopes M.env M.sig M.conv
open T using (Declared; dt[]; dt∷; Arguments; as[]; as∷)
module I = T.Instantiation M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final

Π : Ctx 1
Π = extend ⟨⟩ (tm-type l0)
Φ : Ctx 2
Φ = extend Π (tm-var 0)

parameters fields : Telescope
parameters = ("A" , tm-type l0) ∷ []
fields = ("x" , tm-var 0) ∷ []

parameter-declarations : Declared ⟨⟩ parameters Π
parameter-declarations = dt∷ sc-type (⇒-type refl) dt[]
field-declarations : Declared Π fields Φ
field-declarations = dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[]

-- The same (A : Type0, x : A) may be checked as one field telescope.
declarations : Declared ⟨⟩ Earlier.dependent-tele Φ
declarations = dt∷ sc-type (⇒-type refl) field-declarations
arguments : Arguments ⟨⟩ [] (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) Earlier.dependent-tele
arguments = as∷ (⇐-infer ⇒-atom_type (M.eq-refl {tm-type l0}))
  (as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type})) as[])

-- Entry kinds are DERIVED from declarations, not repeated in Arguments.
derived-checked :
  T.D.Checked ⟨⟩ [] (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) Earlier.dependent-tele
derived-checked = proj₁ (I.instantiate declarations refl arguments
  (ft∷ f-atom_type (ft∷ f-atom_lit ft[])) (λ ()))

parameter-arguments : Arguments ⟨⟩ [] (tm-atom_type ∷ []) parameters
parameter-arguments = as∷ (⇐-infer ⇒-atom_type (M.eq-refl {tm-type l0})) as[]
field-arguments : Arguments ⟨⟩ (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ []) fields
field-arguments = as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type})) as[]

-- The local value's type is the OTHER binder, not a closed stand-in.
local-value : Φ ⊢ tm-var 0 ⇒ tm-var 1
local-value = ⇒-var Fin.zero
typed-result-value : ⟨⟩ ⊢ tm-atom_lit "payload" ⇒ tm-atom_type
typed-result-value = I.instantiate-result⇒ parameter-declarations field-declarations
  parameter-arguments field-arguments (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit ft[]) local-value

typed-result-type : ⟨⟩ ⊢ tm-atom_type ⇒ tm-type l0
typed-result-type = I.instantiate-result⇒ parameter-declarations field-declarations
  parameter-arguments field-arguments (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit ft[])
  (⇒-var (Fin.suc Fin.zero))

-- Computed result-index syntax is transported too, without pretending
-- this substitution theorem is an NbE normalization/refinement proof.
computed-index : Term
computed-index = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) (tm-var 1)
computed-index-local : Φ ⊢ computed-index ⇒ tm-type l0
computed-index-local = ⇒-app
  (⇒-lam {c = tm-type l0} (⇒-type refl)
    (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-type l0})))
  (⇒-var (Fin.suc Fin.zero))
computed-index-typed :
  ⟨⟩ ⊢ F.instantiateResult (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ []) computed-index
    ⇒ tm-type l0
computed-index-typed = I.instantiate-result⇒ parameter-declarations field-declarations
  parameter-arguments field-arguments (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit ft[]) computed-index-local
computed-index-converts :
  Conversion._≈_ M.conv
    (F.instantiateResult (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ []) computed-index)
    tm-atom_type
computed-index-converts = M.rc
  {t = F.instantiateResult (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ []) computed-index}
  {t′ = tm-atom_type} β

-- A final actual PARAMETER may still be a beta redex. The result type
-- retains that raw parameter until conversion; no Value premise is used.
redex-parameter : Term
redex-parameter = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-atom_type
redex-converts : Conversion._≈_ M.conv redex-parameter tm-atom_type
redex-converts = M.rc {t = redex-parameter} {t′ = tm-atom_type} β
redex-final : Final redex-parameter
redex-final = f-app (f-lam f-type f-var) f-atom_type
redex-arguments : Arguments ⟨⟩ [] (redex-parameter ∷ []) parameters
redex-arguments = as∷
  (⇐-infer
    (⇒-app (⇒-lam {c = tm-type l0} (⇒-type refl)
      (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-type l0}))) ⇒-atom_type)
    (M.eq-refl {tm-type l0})) as[]
redex-fields : Arguments ⟨⟩ (redex-parameter ∷ []) (tm-atom_lit "payload" ∷ []) fields
redex-fields = as∷ (⇐-infer ⇒-atom_lit
  (Conversion.≈-sym M.conv {t = redex-parameter} {u = tm-atom_type} redex-converts)) as[]
redex-result : ⟨⟩ ⊢ tm-atom_lit "payload" ⇒ redex-parameter
redex-result = I.instantiate-result⇒ parameter-declarations field-declarations
  redex-arguments redex-fields (ft∷ redex-final ft[]) (ft∷ f-atom_lit ft[]) local-value
redex-result-converted : ⟨⟩ ⊢ tm-atom_lit "payload" ⇒ tm-atom_type
redex-result-converted = ⇒-conv redex-result redex-converts

local-lambda :
  Φ ⊢ tm-lam unrestricted tm-atom_type (tm-var 1)
    ⇒ tm-pi unrestricted tm-atom_type (tm-var 2)
local-lambda = ⇒-lam ⇒-atom_type
  (⇐-infer (⇒-var (Fin.suc Fin.zero)) (M.eq-refl {tm-var 2}))
typed-capture :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-atom_lit "payload")
    ⇒ tm-pi unrestricted tm-atom_type tm-atom_type
typed-capture = I.instantiate-result⇒ parameter-declarations field-declarations
  parameter-arguments field-arguments (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit ft[]) local-lambda
checked-capture :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-atom_lit "payload")
    ⇐ tm-pi unrestricted tm-atom_type tm-atom_type
checked-capture = I.instantiate-result⇐
  {T = tm-pi unrestricted tm-atom_type (tm-var 2)} parameter-declarations field-declarations
  parameter-arguments field-arguments (ft∷ f-atom_type ft[]) (ft∷ f-atom_lit ft[])
  (⇐-lam {c = tm-var 2} ⇒-atom_type (⇐-infer (⇒-var (Fin.suc Fin.zero)) (M.eq-refl {tm-var 2})))

-- The caller may itself be open: x denotes its variable, not a local
-- declaration variable. Under the lambda that caller variable shifts.
Γ : Ctx 1
Γ = extend ⟨⟩ tm-atom_type
open-parameters : Arguments Γ [] (tm-atom_type ∷ []) parameters
open-parameters = as∷ (⇐-infer ⇒-atom_type (M.eq-refl {tm-type l0})) as[]
open-fields : Arguments Γ (tm-atom_type ∷ []) (tm-var 0 ∷ []) fields
open-fields = as∷ (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-atom_type})) as[]
open-result : Γ ⊢ tm-var 0 ⇒ tm-atom_type
open-result = I.instantiate-result⇒ parameter-declarations field-declarations
  open-parameters open-fields (ft∷ f-atom_type ft[]) (ft∷ f-var ft[]) local-value
open-capture :
  Γ ⊢ tm-lam unrestricted tm-atom_type (tm-var 1)
    ⇒ tm-pi unrestricted tm-atom_type tm-atom_type
open-capture = I.instantiate-result⇒ parameter-declarations field-declarations
  open-parameters open-fields (ft∷ f-atom_type ft[]) (ft∷ f-var ft[]) local-lambda

-- Two parameters with DISTINCT actual types, followed by two fields.
-- Correct local frame: [y, x, B, A], not [x, y, A, B].
Π₂ : Ctx 2
Π₂ = extend Π (tm-type l0)
Φ₁ : Ctx 3
Φ₁ = extend Π₂ (tm-var 1)
Φ₂ : Ctx 4
Φ₂ = extend Φ₁ (tm-var 1)
parameters₂ fields₂ : Telescope
parameters₂ = ("A" , tm-type l0) ∷ ("B" , tm-type l0) ∷ []
fields₂ = ("x" , tm-var 1) ∷ ("y" , tm-var 1) ∷ []
parameter-declarations₂ : Declared ⟨⟩ parameters₂ Π₂
parameter-declarations₂ = dt∷ sc-type (⇒-type refl) (dt∷ sc-type (⇒-type refl) dt[])
field-declarations₂ : Declared Π₂ fields₂ Φ₂
field-declarations₂ =
  dt∷ (sc-var (s≤s (s≤s z≤n))) (⇒-var (Fin.suc Fin.zero))
    (dt∷ (sc-var (s≤s (s≤s z≤n))) (⇒-var (Fin.suc Fin.zero)) dt[])
parameter-arguments₂ :
  Arguments ⟨⟩ [] (tm-atom_type ∷ tm-float_type ∷ []) parameters₂
parameter-arguments₂ =
  as∷ (⇐-infer ⇒-atom_type (M.eq-refl {tm-type l0}))
    (as∷ (⇐-infer ⇒-float_type (M.eq-refl {tm-type l0})) as[])
field-arguments₂ :
  Arguments ⟨⟩ (tm-float_type ∷ tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_lit ∷ []) fields₂
field-arguments₂ =
  as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type}))
    (as∷ (⇐-infer ⇒-float_lit (M.eq-refl {tm-float_type})) as[])
first-typed-result : ⟨⟩ ⊢ tm-atom_lit "payload" ⇒ tm-atom_type
first-typed-result = I.instantiate-result⇒ parameter-declarations₂ field-declarations₂
  parameter-arguments₂ field-arguments₂ (ft∷ f-atom_type (ft∷ f-float_type ft[]))
  (ft∷ f-atom_lit (ft∷ f-float_lit ft[])) (⇒-var (Fin.suc Fin.zero))
last-typed-result : ⟨⟩ ⊢ tm-float_lit ⇒ tm-float_type
last-typed-result = I.instantiate-result⇒ parameter-declarations₂ field-declarations₂
  parameter-arguments₂ field-arguments₂ (ft∷ f-atom_type (ft∷ f-float_type ft[]))
  (ft∷ f-atom_lit (ft∷ f-float_lit ft[])) (⇒-var Fin.zero)

atom-at-float : ∀ {n} {Δ : Ctx n} {A}
  → Δ ⊢ tm-atom_lit "payload" ⇒ A → Conversion._≈_ M.conv A tm-float_type → ⊥
atom-at-float ⇒-atom_lit eq with Conversion.≈-heads M.conv ty-atom ty-float eq
... | ()
atom-at-float (⇒-conv {T = A} {T′ = B} der eq′) eq =
  atom-at-float der (Conversion.≈-trans M.conv {t = A} {u = B} {v = tm-float_type} eq′ eq)
atom-at-float (⇒-cumul der le) eq with Conversion.≈-heads M.conv ty-universe ty-float eq
... | ()
wrong-parameter-order-rejected :
  Arguments ⟨⟩ (tm-atom_type ∷ tm-float_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-float_lit ∷ []) fields₂ → ⊥
wrong-parameter-order-rejected (as∷ bad rest) =
  atom-at-float (M.P.check-infer (λ name ()) bad) (M.eq-refl {tm-float_type})

-- These argument checks really exist, but their declaration cannot be
-- admitted: Type2 has no kind. The new theorem cannot bypass that gate.
ill-kinded-arguments :
  Arguments ⟨⟩ [] (tm-type l1 ∷ []) (("x" , tm-type l2) ∷ [])
ill-kinded-arguments = as∷
  (⇐-infer (⇒-type refl) (M.eq-refl {tm-type l2})) as[]
ill-kinded-declaration-rejected : ∀ {d} {Δ : Ctx d}
  → Declared ⟨⟩ (("x" , tm-type l2) ∷ []) Δ → ⊥
ill-kinded-declaration-rejected (dt∷ scoped kind rest) = Earlier.ceiling-not-inferable kind
forward-reference-rejected : ∀ {d} {Δ : Ctx d}
  → Declared ⟨⟩ (("x" , tm-var 0) ∷ []) Δ → ⊥
forward-reference-rejected (dt∷ (sc-var ()) kind rest)
missing-field-rejected : Arguments ⟨⟩ (tm-atom_type ∷ []) [] fields → ⊥
missing-field-rejected ()
extra-field-rejected : Arguments ⟨⟩ [] (tm-atom_lit "payload" ∷ []) [] → ⊥
extra-field-rejected ()

-- Development holes check at any type, so finality is an essential
-- premise of the coherent-frame theorem, not a consequence of Arguments.
hole-arguments : Arguments ⟨⟩ (tm-atom_type ∷ []) (tm-hole "pending" ∷ []) fields
hole-arguments = as∷ ⇐-hole as[]
hole-arguments-not-final : FinalTerms (tm-hole "pending" ∷ []) → ⊥
hole-arguments-not-final (ft∷ () rest)
