{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- An INDEX-DEPENDENT motive: D(A; x:A, B:Type0, y:B) eliminates to B.
-- These prove selected-reduct typing and goal agreement, NOT whole-case
-- motive well-formedness or coverage in unified Core typing.
------------------------------------------------------------------------
module Proof.MotiveAgreementExamples where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Reduction
open import Core.Typing using (⟨⟩; Conversion)
open import Core.TypeHeads using (ty-float; ty-atom)
open import Proof.Progress using (ft[]; ft∷; f-atom_type; f-atom_lit)
import Proof.SoundnessModel as M
import Proof.DependentRegistryExamples as G
import Proof.DependentResultExamples as X
import Proof.DependentInstantiationExamples as E
import Proof.DependentBranchExamples as Earlier
import Proof.MotiveAgreement as Motive

open Core.Typing.Typing M.env M.sig M.conv
module A = Motive.Agreement M.env M.sig M.conv G.registry
  M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final
open G.L.T using (as[]; as∷)

-- Parameter terms are in the CALLER; x/B/y/scrutinee are four new binders.
-- B is index 2 after binding the scrutinee, not the y/scrutinee value.
index-motive : Term → Term
index-motive parameter =
  tm-lam unrestricted parameter
    (tm-lam unrestricted (tm-type l0)
      (tm-lam unrestricted (tm-var 0)
        (tm-lam unrestricted
          (tm-data "LocalResult" (shift 3 0 parameter ∷ []) (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []))
          (tm-var 2))))

steps-convert : ∀ {t u} → _⇝*_ M.sig t u → Conversion._≈_ M.conv t u
steps-convert {t} ⇝*-refl = M.eq-refl {t}
steps-convert {t} {u} (⇝*-step {u = middle} step rest) =
  Conversion.≈-trans M.conv {t = t} {u = middle} {v = u}
    (M.rc {t = t} {t′ = middle} step) (steps-convert rest)

fresh-steps : _⇝*_ M.sig (A.branch-goal G.application (index-motive tm-atom_type)) (tm-var 1)
fresh-steps = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
fresh-check :
  A.O.branch-context G.application ⊢ tm-var 0 ⇐ A.branch-goal G.application (index-motive tm-atom_type)
fresh-check = ⇐-infer (⇒-var Fin.zero)
  (Conversion.≈-sym M.conv {t = A.branch-goal G.application (index-motive tm-atom_type)} {u = tm-var 1}
    (steps-convert fresh-steps))
contracted : ⟨⟩ ⊢ tm-float_lit ⇐ A.result-goal G.application (index-motive tm-atom_type)
contracted = A.contract-at-motive {body = tm-var 0} G.application (index-motive tm-atom_type) fresh-check
actual-steps :
  _⇝*_ M.sig (A.result-goal G.application (index-motive tm-atom_type)) tm-float_type
actual-steps = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
ordinary-alignment :
  substArgs (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
    (A.branch-goal G.application (index-motive tm-atom_type))
    ≡ A.result-goal G.application (index-motive tm-atom_type)
ordinary-alignment = A.goal-agreement G.application (index-motive tm-atom_type)

-- The first result index is itself computed, not just a fresh variable.
computed-fresh-steps :
  _⇝*_ M.sig (A.branch-goal G.computed-application (index-motive tm-atom_type)) (tm-var 1)
computed-fresh-steps = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
computed-contracted :
  ⟨⟩ ⊢ tm-float_lit ⇐ A.result-goal G.computed-application (index-motive tm-atom_type)
computed-contracted = A.contract-at-motive {body = tm-var 0}
  G.computed-application (index-motive tm-atom_type)
  (⇐-infer (⇒-var Fin.zero)
    (Conversion.≈-sym M.conv {t = A.branch-goal G.computed-application (index-motive tm-atom_type)}
      {u = tm-var 1} (steps-convert computed-fresh-steps)))

-- An open caller parameter survives weakening of the whole motive.
open-fresh-steps :
  _⇝*_ M.sig (A.branch-goal Earlier.open-application (index-motive (tm-var 1))) (tm-var 1)
open-fresh-steps = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
open-contracted :
  E.Φ ⊢ tm-float_lit ⇐ A.result-goal Earlier.open-application (index-motive (tm-var 1))
open-contracted = A.contract-at-motive {body = tm-var 0}
  Earlier.open-application (index-motive (tm-var 1))
  (⇐-infer (⇒-var Fin.zero)
    (Conversion.≈-sym M.conv {t = A.branch-goal Earlier.open-application (index-motive (tm-var 1))}
      {u = tm-var 1} (steps-convert open-fresh-steps)))

-- Same motive and declaration, DIFFERENT B index and y type.
alternate : G.L.Application ⟨⟩ "LocalMk" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-atom_lit "other" ∷ [])
alternate = record
  { registry-valid = G.checked-registry ; family = G.family ; ctor = X.ctor ; found = refl
  ; parameters = E.parameter-arguments
  ; fields = as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type}))
      (as∷ (⇐-infer ⇒-atom_type (M.eq-refl {tm-type l0}))
        (as∷ (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type})) as[]))
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ f-atom_type (ft∷ f-atom_lit ft[])) }
alternate-contracted :
  ⟨⟩ ⊢ tm-atom_lit "other" ⇐ A.result-goal alternate (index-motive tm-atom_type)
alternate-contracted = A.contract-at-motive {body = tm-var 0} alternate (index-motive tm-atom_type) fresh-check
alternate-steps :
  _⇝*_ M.sig (A.result-goal alternate (index-motive tm-atom_type)) tm-atom_type
alternate-steps = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
index-really-matters :
  Conversion._≈_ M.conv (A.result-goal G.application (index-motive tm-atom_type))
    (A.result-goal alternate (index-motive tm-atom_type)) → ⊥
index-really-matters equal with Conversion.≈-heads M.conv
  {t = tm-float_type} {u = tm-atom_type} ty-float ty-atom
  (Conversion.≈-trans M.conv {t = tm-float_type}
    {u = A.result-goal G.application (index-motive tm-atom_type)} {v = tm-atom_type}
    (Conversion.≈-sym M.conv {t = A.result-goal G.application (index-motive tm-atom_type)}
      {u = tm-float_type} (steps-convert actual-steps))
    (Conversion.≈-trans M.conv {t = A.result-goal G.application (index-motive tm-atom_type)}
      {u = A.result-goal alternate (index-motive tm-atom_type)} {v = tm-atom_type}
      equal (steps-convert alternate-steps)))
... | ()

-- This is a real raw iota witness, not an extra source typing premise.
selected-iota : _⇝_ M.sig
  (tm-case (tm-ctor "LocalMk" (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []))
    (index-motive tm-atom_type) (("LocalMk" , 3 , tm-var 0) ∷ []))
  tm-float_lit
selected-iota = A.selected-step G.application (tm-var 0) (index-motive tm-atom_type) []
