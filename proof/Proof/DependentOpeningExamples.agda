{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Typed fresh CALLER contexts and direct ambient-variable contraction.
-- These witnesses do not assume motive/index agreement or whole-case typing.
------------------------------------------------------------------------
module Proof.DependentOpeningExamples where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Typing using (Ctx; ⟨⟩; lookup)
open import Core.Reduction using (substArgs)
open import Proof.Progress using (ft[]; ft∷; f-atom_type; f-atom_lit; f-float_type; f-float_lit)
import Proof.SoundnessModel as M
import Proof.DependentRegistryExamples as G
import Proof.DependentResultExamples as X
import Proof.DependentInstantiationExamples as E
import Proof.DependentBranchExamples as Earlier
import Proof.DependentOpening as Opening

open Core.Typing.Typing M.env M.sig M.conv
module O = Opening.Typed M.env M.sig M.conv G.registry
  M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final
open G.L.T using (as[]; as∷)

closed-context : Ctx 3
closed-context = O.branch-context G.application
closed-kinded : O.Kinded (Opening.Opening.trace (O.branch-opening G.application))
closed-kinded = O.branch-kinded G.application
last-field-type : lookup closed-context Fin.zero ≡ tm-var 1
last-field-type = refl
first-field-type : lookup closed-context (Fin.suc (Fin.suc Fin.zero)) ≡ tm-atom_type
first-field-type = refl
fresh-B-not-prematurely-specialized : lookup closed-context Fin.zero ≡ tm-float_type → ⊥
fresh-B-not-prematurely-specialized ()
last-field-contracted : ⟨⟩ ⊢ tm-float_lit ⇒ tm-float_type
last-field-contracted = O.contract-branch⇒ {body = tm-var 0} {T = tm-var 1}
  G.application (⇒-var Fin.zero)

-- Unlike the declaration's A, this caller's unrelated ambient Atom value
-- is outside ALL fields. The field x is a distinct literal payload.
ambient-application : G.L.Application E.Γ "LocalMk" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
ambient-application = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.ctor ; found = refl
  ; parameters = E.open-parameters
  ; fields = as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type}))
      (as∷ (⇐-infer ⇒-float_type (M.eq-refl {tm-type l0}))
        (as∷ (⇐-infer ⇒-float_lit (M.eq-refl {tm-float_type})) as[]))
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[])) }
ambient-context : Ctx 4
ambient-context = O.branch-context ambient-application
ambient-kinded : O.Kinded (Opening.Opening.trace (O.branch-opening ambient-application))
ambient-kinded = O.branch-kinded ambient-application
ambient-branch : ambient-context ⊢ tm-var 3 ⇒ tm-atom_type
ambient-branch = ⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
ambient-contracted : E.Γ ⊢ tm-var 0 ⇒ tm-atom_type
ambient-contracted = O.contract-branch⇒ {body = tm-var 3} {T = tm-atom_type}
  ambient-application ambient-branch
field-contracted : E.Γ ⊢ tm-atom_lit "payload" ⇒ tm-atom_type
field-contracted = O.contract-branch⇒ {body = tm-var 2} {T = tm-atom_type}
  ambient-application (⇒-var (Fin.suc (Fin.suc Fin.zero)))
ambient-is-not-field :
  substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) (tm-var 3)
    ≡ substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) (tm-var 2) → ⊥
ambient-is-not-field ()
ambient-lambda :
  E.Γ ⊢ tm-lam unrestricted tm-atom_type (tm-var 1)
    ⇒ tm-pi unrestricted tm-atom_type tm-atom_type
ambient-lambda = O.contract-branch⇒
  {body = tm-lam unrestricted tm-atom_type (tm-var 4)}
  {T = tm-pi unrestricted tm-atom_type tm-atom_type}
  ambient-application
  (⇒-lam {c = tm-atom_type} ⇒-atom_type
    (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) (M.eq-refl {tm-atom_type})))
own-lambda :
  E.Γ ⊢ tm-lam unrestricted tm-atom_type (tm-var 0)
    ⇒ tm-pi unrestricted tm-atom_type tm-atom_type
own-lambda = O.contract-branch⇒
  {body = tm-lam unrestricted tm-atom_type (tm-var 0)}
  {T = tm-pi unrestricted tm-atom_type tm-atom_type}
  ambient-application
  (⇒-lam {c = tm-atom_type} ⇒-atom_type
    (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-atom_type})))

-- An open actual parameter appears as an ambient type variable, not as an
-- extra field binder. Its caller context has A and x, plus three fields.
parameter-context : Ctx 5
parameter-context = O.branch-context Earlier.open-application
parameter-kinded : O.Kinded (Opening.Opening.trace (O.branch-opening Earlier.open-application))
parameter-kinded = O.branch-kinded Earlier.open-application
parameter-embedded : parameter-context ⊢ tm-var 4 ⇐ tm-type l0
parameter-embedded = O.local-to-branch {body = tm-var 3} {T = tm-type l0}
  Earlier.open-application
  (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) (M.eq-refl {tm-type l0}))
parameter-contracted : E.Φ ⊢ tm-var 1 ⇐ tm-type l0
parameter-contracted = O.contract-branch {body = tm-var 4} {T = tm-type l0}
  Earlier.open-application parameter-embedded
specialized-lambda :
  parameter-context ⊢ tm-lam unrestricted (tm-var 4) (tm-var 3)
    ⇐ tm-pi unrestricted (tm-var 4) (tm-var 5)
specialized-lambda = O.local-to-branch
  {body = Earlier.local-lambda} {T = Earlier.local-lambda-type}
  Earlier.open-application Earlier.local-lambda-typed
specialized-lambda-contracted :
  E.Φ ⊢ tm-lam unrestricted (tm-var 1) (tm-var 1)
    ⇐ tm-pi unrestricted (tm-var 1) (tm-var 2)
specialized-lambda-contracted = O.contract-branch
  {body = tm-lam unrestricted (tm-var 4) (tm-var 3)}
  {T = tm-pi unrestricted (tm-var 4) (tm-var 5)}
  Earlier.open-application specialized-lambda
