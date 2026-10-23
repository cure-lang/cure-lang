{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Residual-form classification is separate from scope, typing and full
-- neutral-case evaluator/readback refinement. Actual calls are fixed.
------------------------------------------------------------------------
module Proof.ResidualNormalExamples where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l2)
open import Core.Signature using (just-inj)
open import Core.NativeRecipe
open import Core.Typing using (⟨⟩)
import Core.DependentTyping as Native
open import Core.Reduction
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ResidualNormal as N
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.BranchOpening as Opening
import Core.CallerAdmission as Caller
import Proof.ResidualNormal as Model
import Proof.BranchOpening as Branch
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotationExamples as Quotation
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as Existing
import Fixtures.ExecutableResidualNormal as Observed
module C = Previous.C
module A = Model.Administrative C.W.sig
module BranchSimulation = Branch.Simulation C.W.sig

module Form (term : Term) (accepted : present (N.check C.W.sig term) ≡ true) where
  evidence : N.Normal C.W.sig term
  evidence = pick (N.check C.W.sig term) accepted
  administrative : ∀ {endpoint} (step : _⇝_ C.W.sig term endpoint) → A.Step step
  administrative = A.normal-step evidence
  invariant : ∀ {endpoint} → _⇝*_ C.W.sig term endpoint → term ≡ endpoint
  invariant = A.path-invariant evidence
module OpaqueCase = Form Observed.opaque-quoted refl
module BranchCase = Form Observed.branch-quoted refl
module MotiveCase = Form Observed.motive-quoted refl
module Nested = Form Observed.nested-quoted refl
module Lambda = Form Observed.lambda-quoted refl
module Ctor = Form Observed.ctor-quoted refl
module DataCase = Form Observed.data-quoted refl
module Open = Form Observed.open-quoted refl
module Beta = Form Observed.beta-quoted refl

global-scrutinee : Term
global-scrutinee = tm-global "Boundary#packed"
case-conversion : ConvRecipe
case-conversion = c-trans
  (tm-app (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])) tm-atom_type) global-scrutinee)
  (c-app c-beta c-refl) c-beta
raw-case-recipe : Recipe
raw-case-recipe = r-case r-leaf [] (r-leaf ∷ []) l0 Recipes.case-kind-recipe Recipes.case-motive-recipe
  Recipes.unpack-case-branches
case-recipe : Recipe
case-recipe = r-convert tm-atom_type case-conversion raw-case-recipe
branch-recipe : Recipe
branch-recipe = r-convert tm-atom_type case-conversion
  (r-case r-leaf [] (r-leaf ∷ []) l0 Recipes.case-kind-recipe Recipes.case-motive-recipe
    ((Recipes.case-field-recipes ,
       r-convert (Native.branchGoal "Boundary#Pack" [] Existing.pack Existing.motive-term)
         Recipes.pack-conversion (r-app (r-lam r-leaf r-leaf) r-leaf)) ∷
     (Recipes.case-field-recipes ,
       r-convert (Native.branchGoal "Boundary#Alternate" [] Existing.alternate Existing.motive-term)
         Recipes.alternate-conversion r-leaf) ∷ []))
module OpaqueNative = Previous.Native Observed.opaque-program tm-atom_type case-recipe r-leaf refl
module BranchNative = Previous.Native Observed.branch-program tm-atom_type branch-recipe r-leaf refl
module LambdaNative = Previous.Native Observed.lambda-program
  (tm-pi unrestricted tm-atom_type tm-atom_type) (r-lam r-leaf case-recipe) (r-pi r-leaf r-leaf) refl
module CtorNative = Previous.Native Observed.ctor-program Existing.goal
  (r-ctor [] [] (r-leaf ∷ case-recipe ∷ [])) (r-data [] (r-leaf ∷ [])) refl
module BetaNative = Previous.Native Observed.beta-program tm-atom_type
  (r-app (r-lam r-leaf r-leaf) r-leaf) r-leaf refl
opaque-safe : C.Sound.SafeState Observed.opaque-quoted tm-atom_type
opaque-safe = OpaqueNative.safe ⇝*-refl
lambda-safe : C.Sound.SafeState Observed.lambda-quoted (tm-pi unrestricted tm-atom_type tm-atom_type)
lambda-safe = LambdaNative.safe ⇝*-refl
ctor-safe : C.Sound.SafeState Observed.ctor-quoted Existing.goal
ctor-safe = CtorNative.safe ⇝*-refl
module BetaReadback = Quotation.Case 0 Observed.beta-program [] (E.v-atom "payload") Observed.beta-quoted
  refl refl refl
beta-safe : C.Sound.SafeState Observed.beta-quoted tm-atom_type
beta-safe = BetaNative.safe (BetaReadback.path Scope.s[] Meaning.d[])

-- Branch beta normalization comes from the GENERAL scoped fresh-opening
-- theorem; only the native outer case congruence is assembled here.
branch-body : Term
branch-body = tm-app (tm-lam unrestricted (tm-var 1) (tm-var 0)) (tm-var 0)
branch-execution : Q.Normalizes 2 (Opening.environment 0 2 []) branch-body (tm-var 0)
branch-execution = Quotation.extract
  (Q.normalise-with C.W.ind 64 2 branch-body (Opening.environment 0 2 [])) (tm-var 0) refl
branch-path : _⇝*_ C.W.sig branch-body (tm-var 0)
branch-path = BranchSimulation.quotation Scope.s[] (pick (scope? 2 branch-body) refl) Meaning.d[] branch-execution
branch-readback-path : _⇝*_ C.W.sig Observed.branch-program Observed.branch-quoted
branch-readback-path = ⇝*-step (ξ-case-brs (⇝ᵇ-cons branch-path (⇝ᵇ-cons ⇝*-refl ⇝ᵇ-nil))) ⇝*-refl
branch-safe : C.Sound.SafeState Observed.branch-quoted tm-atom_type
branch-safe = BranchNative.safe branch-readback-path

stutter : _⇝_ C.W.sig Observed.opaque-quoted Observed.opaque-quoted
stutter = Branch.case-self-step C.W.sig _ _ _
stutter-administrative : A.Step stutter
stutter-administrative = OpaqueCase.administrative stutter
two-stutters : _⇝*_ C.W.sig Observed.opaque-quoted Observed.opaque-quoted
two-stutters = ⇝*-step stutter (⇝*-step stutter ⇝*-refl)
stuttering-path-is-administrative : A.Path two-stutters
stuttering-path-is-administrative = A.normal-path OpaqueCase.evidence two-stutters
finite-path-invariant : ∀ {endpoint} → _⇝*_ C.W.sig Observed.opaque-quoted endpoint
  → Observed.opaque-quoted ≡ endpoint
finite-path-invariant = OpaqueCase.invariant

delta-quoted-unchanged : Observed.delta-quoted ≡ Observed.delta-program
delta-quoted-unchanged = refl
delta-ready-rejected : present (N.check C.W.sig Observed.delta-quoted) ≡ false
delta-ready-rejected = refl
delta-absent-accepted : present (N.check Model.no-delta Observed.delta-quoted) ≡ true
delta-absent-accepted = refl
delta-step : _⇝_ C.W.sig Observed.delta-quoted (tm-atom_lit "answer")
delta-step = δ refl
delta-not-administrative : A.Step delta-step → ⊥
delta-not-administrative ()
delta-different : Observed.delta-quoted ≢ tm-atom_lit "answer"
delta-different ()
delta-not-normal : N.Normal C.W.sig Observed.delta-quoted → ⊥
delta-not-normal normal = A.no-changing-step normal delta-step delta-different

-- Endpoint equality ALONE would misclassify this computational beta loop.
-- Only the total syntax checker/proof sees omega, never actual Eval.
omega-step : _⇝_ C.W.sig Previous.omega Previous.omega
omega-step = β
omega-step-not-administrative : A.Step omega-step → ⊥
omega-step-not-administrative ()
omega-not-normal : N.Normal C.W.sig Previous.omega → ⊥
omega-not-normal normal = omega-step-not-administrative (A.normal-step normal omega-step)
omega-check-rejects : present (N.check C.W.sig Previous.omega) ≡ false
omega-check-rejects = refl
beta-source-rejected : present (N.check C.W.sig Observed.beta-program) ≡ false
beta-source-rejected = refl
zeta-source-rejected : present (N.check C.W.sig
  (tm-let unrestricted tm-atom_type (tm-atom_lit "payload") (tm-var 0))) ≡ false
zeta-source-rejected = refl
iota-source-rejected : present (N.check C.W.sig
  (tm-case Existing.value tm-atom_type (("Boundary#Pack" , 2 , tm-atom_lit "payload") ∷ []))) ≡ false
iota-source-rejected = refl
branch-redex-rejected : present (N.check C.W.sig Observed.branch-program) ≡ false
branch-redex-rejected = refl
motive-redex-rejected : present (N.check C.W.sig Observed.motive-program) ≡ false
motive-redex-rejected = refl
unscoped-form-can-pass : present (N.check C.W.sig (tm-var 3)) ≡ true
unscoped-form-can-pass = refl
scope-still-rejects : present (scope? 0 (tm-var 3)) ≡ false
scope-still-rejects = refl
unkindable-form-can-pass : present (N.check C.W.sig (tm-type l2)) ≡ true
unkindable-form-can-pass = refl
kind-still-rejects : present (Previous.CallerReplay.C.W.G.D.kind ⟨⟩ (tm-type l2) r-leaf) ≡ false
kind-still-rejects = refl
ill-typed-data-normal : present (N.check C.W.sig Observed.data-quoted) ≡ true
ill-typed-data-normal = refl
ill-typed-data-rejected : present (Previous.CallerReplay.verify
  (Caller.request [] [] [] [] Observed.data-quoted (tm-type l0) (r-data [] (case-recipe ∷ [])) r-leaf)) ≡ false
ill-typed-data-rejected = refl
unsupported-leaf-not-a-redex-verdict : present (N.check C.W.sig tm-float_type) ≡ false
unsupported-leaf-not-a-redex-verdict = refl
shared-neutral-readback-still-excluded : Previous.failure (E.run-with C.W.ind 64 Observed.opaque-program [])
  ≡ just E.neutral-scrutinee
shared-neutral-readback-still-excluded = refl

-- Even a computational delta self-loop has no changing global endpoints.
-- The sufficient grammar still rejects it; no completeness/termination
-- claim follows from endpoint invariance alone.
loop-sig : Signature
loop-sig = record { body = λ name → just (tm-global name) ; type-of = λ _ → nothing }
delta-loop-endpoints-agree : ∀ {endpoint} → _⇝_ loop-sig (tm-global "loop") endpoint
  → tm-global "loop" ≡ endpoint
delta-loop-endpoints-agree (δ found) = just-inj found
delta-loop-rejected : present (N.check loop-sig (tm-global "loop")) ≡ false
delta-loop-rejected = refl
strict-embedding-preserved : N.Normal Model.no-delta (tm-lam unrestricted tm-atom_type (tm-var 0))
strict-embedding-preserved = Model.strict-embedding
  (Q.normal-lam Q.normal-atom-type (Q.normal-neutral Q.normal-var))
