{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Typed SELECTED-branch contraction and its fields-only runtime frame.
-- The raw iota witnesses below do not assert full source-case typing.
------------------------------------------------------------------------
module Proof.DependentBranchExamples where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Reduction
open import Core.Signature using (just-inj)
open import Core.Typing using (⟨⟩)
open import Proof.Progress
  using (Final; ft[]; ft∷; f-var; f-lam; f-float_type; f-float_lit)
import Core.LocalFrame as F
import Proof.SoundnessModel as M
import Proof.DependentRegistryExamples as G
import Proof.DependentResultExamples as X
import Proof.DependentInstantiationExamples as E
import Proof.DependentBranch as Branch

open Core.Typing.Typing M.env M.sig M.conv
module B = Branch.Contract M.env M.sig M.conv G.registry
  M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final
open G.L.T using (as[]; as∷)

last-field-typed : ⟨⟩ ⊢ tm-float_lit ⇒ tm-float_type
last-field-typed = B.contract-infers {body = tm-var 0} {T = tm-var 1} G.application f-var
  (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-var 1}))
parameter-typed : ⟨⟩ ⊢ tm-atom_type ⇒ tm-type l0
parameter-typed = B.contract-infers {body = tm-var 3} {T = tm-type l0} G.application f-var
  (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) (M.eq-refl {tm-type l0}))
parameter-specialized : B.runtime-body G.application (tm-var 3) ≡ tm-atom_type
parameter-specialized = refl

-- Without specialisation a parameter slot becomes an unrelated ambient
-- variable. Without field protection it can instead become a FIELD value.
unspecialized-parameter :
  substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) (tm-var 3) ≡ tm-var 0
unspecialized-parameter = refl
unspecialized-not-closed :
  Scoped 0 (substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) (tm-var 3)) → ⊥
unspecialized-not-closed (sc-var ())
unprotected-parameter :
  substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
    (F.specializeParameters 0 (tm-atom_type ∷ []) (tm-var 3)) ≡ tm-atom_lit "payload"
unprotected-parameter = refl
unprotected-is-not-parameter :
  substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
    (F.specializeParameters 0 (tm-atom_type ∷ []) (tm-var 3)) ≡ tm-atom_type → ⊥
unprotected-is-not-parameter ()

local-lambda : Term
local-lambda = tm-lam unrestricted (tm-var 3) (tm-var 3)
local-lambda-type : Term
local-lambda-type = tm-pi unrestricted (tm-var 3) (tm-var 4)
local-lambda-typed : X.Φ ⊢ local-lambda ⇐ local-lambda-type
local-lambda-typed = ⇐-lam
  (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) (M.eq-refl {tm-var 4}))
lambda-contracted :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-atom_lit "payload")
    ⇒ tm-pi unrestricted tm-atom_type tm-atom_type
lambda-contracted = B.contract-infers {body = local-lambda} {T = local-lambda-type}
  G.application (f-lam f-var f-var) local-lambda-typed
lambda-final :
  Final (tm-lam unrestricted tm-atom_type (tm-atom_lit "payload"))
lambda-final = B.contract-final {body = local-lambda} G.application (f-lam f-var f-var)
own-lambda-binder :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-var 0)
    ⇒ tm-pi unrestricted tm-atom_type tm-atom_type
own-lambda-binder = B.contract-infers
  {body = tm-lam unrestricted (tm-var 3) (tm-var 0)} {T = local-lambda-type}
  G.application (f-lam f-var f-var)
  (⇐-lam (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
    (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-var 4})))

-- An OPEN caller supplies its A and x variables. Runtime specialisation
-- shifts A past the three fields, then field contraction restores index 1.
open-application : G.L.Application E.Φ "LocalMk" (tm-var 1 ∷ [])
  (tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ [])
open-application = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.ctor ; found = refl
  ; parameters = as∷ (⇐-infer (⇒-var (Fin.suc Fin.zero)) (M.eq-refl {tm-type l0})) as[]
  ; fields = as∷ (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-var 1}))
      (as∷ (⇐-infer ⇒-float_type (M.eq-refl {tm-type l0}))
        (as∷ (⇐-infer ⇒-float_lit (M.eq-refl {tm-float_type})) as[]))
  ; parameters-final = ft∷ f-var ft[]
  ; fields-final = ft∷ f-var (ft∷ f-float_type (ft∷ f-float_lit ft[])) }
open-parameter-shifted : B.runtime-body open-application (tm-var 3) ≡ tm-var 4
open-parameter-shifted = refl
open-parameter-restored : E.Φ ⊢ tm-var 1 ⇒ tm-type l0
open-parameter-restored = B.contract-infers {body = tm-var 3} {T = tm-type l0}
  open-application f-var
  (⇐-infer (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) (M.eq-refl {tm-type l0}))
open-lambda-contracted :
  E.Φ ⊢ tm-lam unrestricted (tm-var 1) (tm-var 1)
    ⇒ tm-pi unrestricted (tm-var 1) (tm-var 2)
open-lambda-contracted = B.contract-infers {body = local-lambda} {T = local-lambda-type}
  open-application (f-lam f-var f-var) local-lambda-typed

-- Actual reduction statements for arbitrary raw motives. No coverage or
-- whole-case typing assertion is hidden in these syntactic witnesses.
iota-parameter : ∀ motive → _⇝_ M.sig
  (tm-case (tm-ctor "LocalMk" (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []))
    motive (("LocalMk" , 3 , tm-atom_type) ∷ [])) tm-atom_type
iota-parameter motive = B.selected-step G.application (tm-var 3) motive []
iota-lambda : ∀ motive → _⇝_ M.sig
  (tm-case (tm-ctor "LocalMk" (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []))
    motive (("LocalMk" , 3 , tm-lam unrestricted tm-atom_type (tm-var 3)) ∷ []))
  (tm-lam unrestricted tm-atom_type (tm-atom_lit "payload"))
iota-lambda motive = B.selected-step G.application local-lambda motive []
parameter-is-not-a-field-arity-aux : ∀ {motive target} → _⇝_ M.sig
  (tm-case (tm-ctor "LocalMk" (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []))
    motive (("LocalMk" , 4 , tm-atom_type) ∷ [])) target → target ≡ tm-atom_type → ⊥
parameter-is-not-a-field-arity-aux (ι found size) same
  with just-inj found
... | refl with size
... | ()
parameter-is-not-a-field-arity-aux (ξ-case step) ()
parameter-is-not-a-field-arity-aux (ξ-case-brs steps) ()
parameter-is-not-a-field-arity-aux (ξ-case-motive step) ()

parameter-is-not-a-field-arity : ∀ {motive} → _⇝_ M.sig
  (tm-case (tm-ctor "LocalMk" (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []))
    motive (("LocalMk" , 4 , tm-atom_type) ∷ [])) tm-atom_type → ⊥
parameter-is-not-a-field-arity step = parameter-is-not-a-field-arity-aux step refl
