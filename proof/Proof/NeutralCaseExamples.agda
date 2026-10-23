{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Positive top-level neutral capture/readback, not a replacement shared
-- value domain. Nested residual limits and phase failures stay explicit.
------------------------------------------------------------------------
module Proof.NeutralCaseExamples where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing; Maybe)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.NativeRecipe
open import Core.Signature using (Ctor)
open import Core.Reduction using (_⇝*_)
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.NeutralCase as Case
import Core.ClosureEval as E
import Core.ClosureScope as Scope
import Core.ResidualNormal as Normal
import Core.CallerAdmission as Caller
import Core.DependentTyping as Native
import Proof.NeutralCase as Model
import Proof.ResidualNormal as Residual
import Proof.ResidualNormalExamples as Prior
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as Existing
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableNeutralCase as Observed
module C = Previous.C
module R = Previous.CallerReplay
module Simulation = Model.Simulation C.W.sig
module Safe = Model.Safe Source.Pin.admission

scrutinee : Term → Term
scrutinee (tm-case s m branches) = s
scrutinee other = other
motive : Term → Term
motive (tm-case s m branches) = m
motive other = other
branches : Term → List Branch
branches (tm-case s m branches) = branches
branches other = []
Run : ℕ → List E.Value → Term → Set
Run depth env program = Σ (Case.Captured env (scrutinee program)) λ cap →
  Case.Readback depth env (scrutinee program) (motive program) (branches program) cap
run : (depth : ℕ) (env : List E.Value) (program : Term) → Case.Result (Run depth env program)
run depth env program = Case.normalise-with C.W.ind 64 depth env (scrutinee program) (motive program) (branches program)
successful : ∀ {A} → Case.Result A → Bool
successful (Case.done out) = true
successful (Case.stop reason) = false
choose : ∀ {A} (result : Case.Result A) → successful result ≡ true → A
choose (Case.done out) proof = out
choose (Case.stop reason) ()
run-term : (depth : ℕ) (env : List E.Value) (program : Term) → Run depth env program → Term
run-term depth env program result = Case.Readback.term (proj₂ result)

module Observation (depth : ℕ) (env actual-env : List E.Value) (program quoted : Term) (head : E.Neutral)
  (shape : program ≡ tm-case (scrutinee program) (motive program) (branches program))
  (same-env : env ≡ actual-env)
  (accepted : successful (run depth env program) ≡ true)
  (same-head : Case.Captured.head (proj₁ (choose (run depth env program) accepted)) ≡ head)
  (same-term : run-term depth env program (choose (run depth env program) accepted) ≡ quoted)
  (scope-ok : present (scope? (length env) program) ≡ true) where
  cap : Case.Captured env (scrutinee program)
  cap = proj₁ (choose (run depth env program) accepted)
  out : Case.Readback depth env (scrutinee program) (motive program) (branches program) cap
  out = proj₂ (choose (run depth env program) accepted)
  source-scope : Scoped (length env) (tm-case (scrutinee program) (motive program) (branches program))
  source-scope = subst (Scoped (length env)) shape (pick (scope? (length env) program) scope-ok)
  scoped : Scoped depth quoted
  scoped = subst (Scoped depth) same-term (Model.scoped out)
  normal : Normal.Normal Residual.no-delta quoted
  normal = subst (Normal.Normal Residual.no-delta) same-term (Model.normal out)
  path : ∀ {images} → Scope.EnvironmentScoped depth env → Meaning.Environments depth env images
    → _⇝*_ C.W.sig (substS (Meaning.environment-sub images) program) quoted
  path {images} scope denoted =
    subst (λ target → _⇝*_ C.W.sig (substS (Meaning.environment-sub images) program) target) same-term
      (Simulation.O.⇝*-source (cong (substS (Meaning.environment-sub images)) (sym shape))
        (Simulation.quotation cap out scope source-scope denoted))

module OpaqueCase = Observation Observed.opaque-depth Observed.opaque-environment Observed.opaque-captured-environment
  Observed.opaque-program Observed.opaque-quoted Observed.opaque-head refl refl refl refl refl refl
module BranchCase = Observation Observed.branch-depth Observed.branch-environment Observed.branch-captured-environment
  Observed.branch-program Observed.branch-quoted Observed.branch-head refl refl refl refl refl refl
module MotiveCase = Observation Observed.motive-depth Observed.motive-environment Observed.motive-captured-environment
  Observed.motive-program Observed.motive-quoted Observed.motive-head refl refl refl refl refl refl
module Scrutinee = Observation Observed.scrutinee-depth Observed.scrutinee-environment Observed.scrutinee-captured-environment
  Observed.scrutinee-program Observed.scrutinee-quoted Observed.scrutinee-head refl refl refl refl refl refl
module Open = Observation Observed.open-depth Observed.open-environment Observed.open-captured-environment
  Observed.open-program Observed.open-quoted Observed.open-head refl refl refl refl refl refl
module Spine = Observation Observed.spine-depth Observed.spine-environment Observed.spine-captured-environment
  Observed.spine-program Observed.spine-quoted Observed.spine-head refl refl refl refl refl refl
module Zero = Observation Observed.zero-depth Observed.zero-environment Observed.zero-captured-environment
  Observed.zero-program Observed.zero-quoted Observed.zero-head refl refl refl refl refl refl
module Multi = Observation Observed.multi-depth Observed.multi-environment Observed.multi-captured-environment
  Observed.multi-program Observed.multi-quoted Observed.multi-head refl refl refl refl refl refl
module Capture = Observation Observed.capture-depth Observed.capture-environment Observed.capture-captured-environment
  Observed.capture-program Observed.capture-quoted Observed.capture-head refl refl refl refl refl refl
module DataCase = Observation Observed.data-depth Observed.data-environment Observed.data-captured-environment
  Observed.data-program Observed.data-quoted Observed.data-head refl refl refl refl refl refl
module SharedCase = Observation Observed.shared-case-depth Observed.shared-case-environment Observed.shared-case-captured-environment
  Observed.shared-case-program Observed.shared-case-quoted Observed.shared-case-head refl refl refl refl refl refl
module DeltaCase = Observation Observed.delta-depth Observed.delta-environment Observed.delta-captured-environment
  Observed.delta-program Observed.delta-quoted Observed.delta-head refl refl refl refl refl refl

opaque-path : _⇝*_ C.W.sig Observed.opaque-program Observed.opaque-quoted
opaque-path = OpaqueCase.path Scope.s[] Meaning.d[]
branch-path : _⇝*_ C.W.sig Observed.branch-program Observed.branch-quoted
branch-path = BranchCase.path Scope.s[] Meaning.d[]
motive-path : _⇝*_ C.W.sig Observed.motive-program Observed.motive-quoted
motive-path = MotiveCase.path Scope.s[] Meaning.d[]
scrutinee-path : _⇝*_ C.W.sig Observed.scrutinee-program Observed.scrutinee-quoted
scrutinee-path = Scrutinee.path Scope.s[] Meaning.d[]
capture-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (tm-atom_lit "payload" ∷ [])) Observed.capture-program) Observed.capture-quoted
capture-path = Capture.path (Scope.s∷ Scope.s-atom Scope.s[]) (Meaning.d∷ Meaning.d-atom Meaning.d[])
spine-path : _⇝*_ C.W.sig Observed.spine-program Observed.spine-quoted
spine-path = Spine.path (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])

-- Native admission is independently replayed, not inferred from capture.
opaque-safe : C.Sound.SafeState Observed.opaque-quoted tm-atom_type
opaque-safe = Safe.safe-readback Prior.OpaqueNative.admitted OpaqueCase.out refl Scope.s[] OpaqueCase.source-scope Meaning.d[]
branch-safe : C.Sound.SafeState Observed.branch-quoted tm-atom_type
branch-safe = Safe.safe-readback Prior.BranchNative.admitted BranchCase.out refl Scope.s[] BranchCase.source-scope Meaning.d[]
case-conversion : Term → ConvRecipe
case-conversion s = c-trans
  (tm-app (tm-lam unrestricted Existing.goal tm-atom_type) s) (c-app c-beta c-refl) c-beta
scrutinee-recipe : Recipe
scrutinee-recipe = r-convert tm-atom_type (case-conversion (scrutinee Observed.scrutinee-program))
  (r-case (r-app (r-lam (r-data [] (r-leaf ∷ [])) r-leaf) r-leaf) [] (r-leaf ∷ []) l0
    Recipes.case-kind-recipe Recipes.case-motive-recipe Recipes.unpack-case-branches)
module ScrutineeNative = Previous.Native Observed.scrutinee-program tm-atom_type scrutinee-recipe r-leaf refl
scrutinee-safe : C.Sound.SafeState Observed.scrutinee-quoted tm-atom_type
scrutinee-safe = Safe.safe-readback ScrutineeNative.admitted Scrutinee.out refl Scope.s[] Scrutinee.source-scope Meaning.d[]

let-motive : Term
let-motive = motive Observed.motive-program
old-top-goal : Term
old-top-goal = Native.apps Existing.motive-term (tm-atom_type ∷ Prior.global-scrutinee ∷ [])
let-branch-recipe : Name → Ctor → ConvRecipe → Recipe
let-branch-recipe name ctor old-conversion =
  r-convert (Native.branchGoal name [] ctor let-motive)
    (c-sym (c-trans (Native.branchGoal name [] ctor Existing.motive-term)
      (c-app (c-app c-zeta c-refl) c-refl) (c-sym old-conversion))) r-leaf
motive-recipe : Recipe
motive-recipe = r-convert tm-atom_type
  (c-trans old-top-goal (c-app (c-app c-zeta c-refl) c-refl) Prior.case-conversion)
  (r-case r-leaf [] (r-leaf ∷ []) l0 Recipes.case-kind-recipe
    (r-let Recipes.case-kind-recipe Recipes.case-motive-recipe r-leaf)
    ((Recipes.case-field-recipes , let-branch-recipe "Boundary#Pack" Existing.pack Recipes.pack-conversion) ∷
     (Recipes.case-field-recipes , let-branch-recipe "Boundary#Alternate" Existing.alternate Recipes.alternate-conversion) ∷ []))
module MotiveNative = Previous.Native Observed.motive-program tm-atom_type motive-recipe r-leaf refl
motive-safe : C.Sound.SafeState Observed.motive-quoted tm-atom_type
motive-safe = Safe.safe-readback MotiveNative.admitted MotiveCase.out refl Scope.s[] MotiveCase.source-scope Meaning.d[]

capture-recipe : Recipe
capture-recipe = r-convert tm-atom_type (case-conversion (scrutinee Observed.capture-program))
  (r-case (r-let r-leaf r-leaf r-leaf) [] (r-leaf ∷ []) l0 Recipes.case-kind-recipe Recipes.case-motive-recipe
    ((Recipes.case-field-recipes ,
      r-convert (Native.branchGoal "Boundary#Pack" [] Existing.pack Existing.motive-term)
        Recipes.pack-conversion (r-let r-leaf r-leaf r-leaf)) ∷
     (Recipes.case-field-recipes ,
      r-convert (Native.branchGoal "Boundary#Alternate" [] Existing.alternate Existing.motive-term)
        Recipes.alternate-conversion (r-let r-leaf r-leaf r-leaf)) ∷ []))
capture-query : Caller.Request
capture-query = Caller.request (("x" , tm-atom_type) ∷ []) (r-leaf ∷ [])
  (tm-atom_lit "payload" ∷ []) (r-leaf ∷ []) Observed.capture-program tm-atom_type capture-recipe r-leaf
capture-checked : R.Checked capture-query
capture-checked = pick (R.verify capture-query) refl
capture-safe : C.Sound.SafeState Observed.capture-quoted tm-atom_type
-- Fix images before refl; inferring them through subst/parser projections
-- can force very expensive inverse elaboration.
capture-safe = Safe.safe-readback {captured = tm-atom_lit "payload" ∷ []} capture-checked Capture.out refl
  (Scope.s∷ Scope.s-atom Scope.s[]) Capture.source-scope (Meaning.d∷ Meaning.d-atom Meaning.d[])
budgets-agree : ∀ budget → R.Checked.run capture-checked budget
  ≡ C.Sound.truncate budget (R.Checked.tree capture-checked)
budgets-agree = R.Checked.budgets-agree capture-checked

actual-signature-normal : present (Normal.check C.W.sig Observed.capture-quoted) ≡ true
actual-signature-normal = refl
delta-signature-boundary : present (Normal.check C.W.sig Observed.delta-quoted) ≡ false
delta-signature-boundary = refl
failure : ∀ {A} → Case.Result A → Maybe Case.Failure
failure (Case.done output) = nothing
failure (Case.stop reason) = just reason
nested-scrutinee-limit : failure (run 0 [] Observed.nested-scrutinee-program)
  ≡ just (Case.capture-failure E.neutral-scrutinee)
nested-scrutinee-limit = refl
nested-branch-limit : failure (run 0 [] Observed.nested-branch-program)
  ≡ just (Case.branch-failure "Boundary#Pack" 2 E.neutral-scrutinee)
nested-branch-limit = refl
non-neutral-is-not-typing-failure : failure (Case.normalise-with C.W.ind 64 0 [] Existing.value
  Existing.motive-term Existing.branches) ≡ just Case.not-neutral
non-neutral-is-not-typing-failure = refl
zero-budget : failure (Case.normalise-with C.W.ind 0 0 [] Prior.global-scrutinee tm-atom_type []) ≡ just Case.exhausted
zero-budget = refl
head-escape : failure (Case.normalise-with C.W.ind 64 0 (E.v-neutral (E.n-var 0) ∷ [])
  (tm-var 0) tm-atom_type []) ≡ just (Case.head-failure E.escaped-level)
head-escape = refl
motive-unbound : failure (Case.normalise-with C.W.ind 64 0 [] Prior.global-scrutinee (tm-var 0) [])
  ≡ just (Case.motive-failure E.unbound)
motive-unbound = refl
zero-arity-unbound : failure (Case.normalise-with C.W.ind 64 0 [] Prior.global-scrutinee tm-atom_type
  (("Boundary#Pack" , 0 , tm-var 0) ∷ [])) ≡ just (Case.branch-failure "Boundary#Pack" 0 E.unbound)
zero-arity-unbound = refl
motive-omega-budget : failure (Case.normalise-with C.W.ind 16 0 [] Prior.global-scrutinee Previous.omega [])
  ≡ just (Case.motive-failure E.exhausted)
motive-omega-budget = refl
branch-omega-budget : failure (Case.normalise-with C.W.ind 16 0 [] Prior.global-scrutinee tm-atom_type
  (("Boundary#Pack" , 2 , Previous.omega) ∷ [])) ≡ just (Case.branch-failure "Boundary#Pack" 2 E.exhausted)
branch-omega-budget = refl
old-shared-api-unchanged : Previous.failure (E.run-with C.W.ind 64 Observed.opaque-program []) ≡ just E.neutral-scrutinee
old-shared-api-unchanged = refl
