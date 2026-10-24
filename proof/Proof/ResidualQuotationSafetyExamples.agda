{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Independent native admission is essential: raw residual normalization
-- alone proves neither typing nor safety. No normalization callback.
------------------------------------------------------------------------
module Proof.ResidualQuotationSafetyExamples where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (just)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.NativeRecipe
open import Core.Grade using (unrestricted)
open import Core.Universe using (Level; l0; l1)
open import Core.Signature using (Ctor)
open import Core.Reduction using (_⇝*_)
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.CallerAdmission as Caller
import Core.DependentTyping as Native
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ResidualQuotation as Model
import Proof.ResidualQuotationExamples as Replay
import Proof.ResidualNormalExamples as Prior
import Proof.NeutralCaseExamples as Old
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as Existing
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableResidualQuotation as Observed
module C = Previous.C
module R = Previous.CallerReplay
module Safe = Model.Safe Source.Pin.admission

-- Five earlier checked callers now use the recursive normalization theorem.
opaque-safe : C.Sound.SafeState Observed.opaque-quoted tm-atom_type
opaque-safe = Safe.safe-normalization {captured = []} Prior.OpaqueNative.admitted Replay.ReplayOpaque.execution
  refl Scope.s[] Replay.ReplayOpaque.source-scope Meaning.d[]
branch-safe : C.Sound.SafeState Observed.branch-quoted tm-atom_type
branch-safe = Safe.safe-normalization {captured = []} Prior.BranchNative.admitted Replay.ReplayBranch.execution
  refl Scope.s[] Replay.ReplayBranch.source-scope Meaning.d[]
motive-safe : C.Sound.SafeState Observed.motive-quoted tm-atom_type
motive-safe = Safe.safe-normalization {captured = []} Old.MotiveNative.admitted Replay.ReplayMotive.execution
  refl Scope.s[] Replay.ReplayMotive.source-scope Meaning.d[]
scrutinee-safe : C.Sound.SafeState Observed.scrutinee-quoted tm-atom_type
scrutinee-safe = Safe.safe-normalization {captured = []} Old.ScrutineeNative.admitted Replay.ReplayScrutinee.execution
  refl Scope.s[] Replay.ReplayScrutinee.source-scope Meaning.d[]
capture-safe : C.Sound.SafeState Observed.capture-quoted tm-atom_type
capture-safe = Safe.safe-normalization {captured = tm-atom_lit "payload" ∷ []}
  Old.capture-checked Replay.ReplayCapture.execution refl (Scope.s∷ Scope.s-atom Scope.s[])
  Replay.ReplayCapture.source-scope (Meaning.d∷ Meaning.d-atom Meaning.d[])

function-type : Term
function-type = tm-pi unrestricted tm-atom_type tm-atom_type
module LambdaNative = Previous.Native Observed.lam-body-program function-type
  (r-lam r-leaf Prior.case-recipe) (r-pi r-leaf r-leaf) refl
lambda-safe : C.Sound.SafeState Observed.lam-body-quoted function-type
lambda-safe = Safe.safe-normalization {captured = []} LambdaNative.admitted Replay.ReplayLamBody.execution
  refl Scope.s[] Replay.ReplayLamBody.source-scope Meaning.d[]
module ConstructorNative = Previous.Native Observed.ctor-field-program Existing.goal
  (r-ctor [] [] (r-leaf ∷ Prior.case-recipe ∷ [])) (r-data [] (r-leaf ∷ [])) refl
constructor-safe : C.Sound.SafeState Observed.ctor-field-quoted Existing.goal
constructor-safe = Safe.safe-normalization {captured = []} ConstructorNative.admitted Replay.ReplayCtorField.execution
  refl Scope.s[] Replay.ReplayCtorField.source-scope Meaning.d[]
module BetaNative = Previous.Native Observed.beta-argument-program tm-atom_type
  (r-app (r-lam r-leaf r-leaf) Prior.case-recipe) r-leaf refl
beta-safe : C.Sound.SafeState Observed.beta-argument-quoted tm-atom_type
beta-safe = Safe.safe-normalization {captured = []} BetaNative.admitted Replay.ReplayBetaArgument.execution
  refl Scope.s[] Replay.ReplayBetaArgument.source-scope Meaning.d[]
module LetNative = Previous.Native Observed.let-capture-program function-type
  (r-let r-leaf Prior.case-recipe (r-lam r-leaf r-leaf)) (r-pi r-leaf r-leaf) refl
let-safe : C.Sound.SafeState Observed.let-capture-quoted function-type
let-safe = Safe.safe-normalization {captured = []} LetNative.admitted Replay.ReplayLetCapture.execution
  refl Scope.s[] Replay.ReplayLetCapture.source-scope Meaning.d[]

old-case-over : Term → Recipe → Recipe
old-case-over scrutinee recipe = r-convert tm-atom_type (Old.case-conversion scrutinee)
  (r-case recipe [] (r-leaf ∷ []) l0 Recipes.case-kind-recipe Recipes.case-motive-recipe Recipes.unpack-case-branches)
exact-recipe : Recipe
exact-recipe = old-case-over (Old.scrutinee Observed.exact-case-program)
  (r-ctor [] [] (r-leaf ∷ Prior.case-recipe ∷ []))
module ExactNative = Previous.Native Observed.exact-case-program tm-atom_type exact-recipe r-leaf refl
exact-safe : C.Sound.SafeState Observed.exact-case-quoted tm-atom_type
exact-safe = Safe.safe-normalization {captured = []} ExactNative.admitted Replay.ReplayExactCase.execution
  refl Scope.s[] Replay.ReplayExactCase.source-scope Meaning.d[]

-- This is a recipe proposal, never asserted equality. Replay checks BOTH
-- beta steps and their intermediate against the actual source/target.
two-beta : Term → ConvRecipe
two-beta (tm-app (tm-app (tm-lam g domain body) index) value) =
  c-trans (tm-app (substTopT index body) value) (c-app c-beta c-refl) c-beta
two-beta other = c-refl
constant-branch : Term → Name → Ctor → Recipe → Recipe
constant-branch motive name ctor body =
  r-convert (Native.branchGoal name [] ctor motive)
    (c-sym (two-beta (Native.branchGoal name [] ctor motive))) body
constant-case : Level → Term → Term → Recipe → Recipe → Recipe
constant-case level program result motive-recipe body-recipe =
  r-convert result (two-beta (Native.apps motive (tm-atom_type ∷ Old.scrutinee program ∷ [])))
    (r-case r-leaf [] (r-leaf ∷ []) level Recipes.case-kind-recipe motive-recipe
      ((Recipes.case-field-recipes , constant-branch motive "Boundary#Pack" Existing.pack body-recipe) ∷
       (Recipes.case-field-recipes , constant-branch motive "Boundary#Alternate" Existing.alternate body-recipe) ∷ []))
  where motive = Old.motive program
packed-case : Term
packed-case = Old.scrutinee Observed.typed-scrutinee-program
packed-recipe : Recipe
packed-recipe = constant-case l1 packed-case Existing.goal
  (r-lam r-leaf (r-lam (r-data [] (r-leaf ∷ [])) (r-data [] (r-leaf ∷ []))))
  (r-ctor [] [] (r-leaf ∷ r-leaf ∷ []))
module NestedScrutineeNative = Previous.Native Observed.typed-scrutinee-program tm-atom_type
  (old-case-over packed-case packed-recipe) r-leaf refl
nested-scrutinee-safe : C.Sound.SafeState Observed.typed-scrutinee-quoted tm-atom_type
nested-scrutinee-safe = Safe.safe-normalization {captured = []}
  NestedScrutineeNative.admitted Replay.ReplayTypedScrutinee.execution
  refl Scope.s[] Replay.ReplayTypedScrutinee.source-scope Meaning.d[]
typed-branch-recipe : Recipe
typed-branch-recipe = constant-case l0 Observed.typed-branch-program tm-atom_type
  (r-lam r-leaf (r-lam (r-data [] (r-leaf ∷ [])) r-leaf)) Prior.case-recipe
module NestedBranchNative = Previous.Native Observed.typed-branch-program tm-atom_type typed-branch-recipe r-leaf refl
nested-branch-safe : C.Sound.SafeState Observed.typed-branch-quoted tm-atom_type
nested-branch-safe = Safe.safe-normalization {captured = []}
  NestedBranchNative.admitted Replay.ReplayTypedBranch.execution
  refl Scope.s[] Replay.ReplayTypedBranch.source-scope Meaning.d[]

-- A real checked argument now closes a caller slot occupied by a residual
-- VALUE. Scope/denotation, not equality to a normalized capture, is needed.
environment-query : Caller.Request
environment-query = Caller.request (("x" , tm-atom_type) ∷ []) (r-leaf ∷ [])
  (Observed.opaque-program ∷ []) (Prior.case-recipe ∷ []) Observed.environment-program function-type
  (r-lam r-leaf r-leaf) (r-pi r-leaf r-leaf)
environment-checked : R.Checked environment-query
environment-checked = pick (R.verify environment-query) refl
opaque-denotes : Meaning.Denotes 0 Observed.opaque-value Observed.opaque-program
opaque-denotes = Meaning.d-neutral (Meaning.d-case Meaning.d-global Meaning.d[])
environment-scope : Scope.EnvironmentScoped 0 Observed.environment-environment
environment-scope = Scope.s∷ (Replay.ReplayOpaque.value-scoped Scope.s[]) Scope.s[]
environment-denotes : Meaning.Environments 0 Observed.environment-environment (Observed.opaque-program ∷ [])
environment-denotes = Meaning.d∷ opaque-denotes Meaning.d[]
environment-safe : C.Sound.SafeState Observed.environment-quoted function-type
environment-safe = Safe.safe-normalization {captured = Observed.opaque-program ∷ []}
  environment-checked Replay.ReplayEnvironment.execution refl environment-scope
  Replay.ReplayEnvironment.source-scope environment-denotes
environment-budgets-agree : ∀ budget → R.Checked.run environment-checked budget
  ≡ C.Sound.truncate budget (R.Checked.tree environment-checked)
environment-budgets-agree = R.Checked.budgets-agree environment-checked

-- Instantiate the general path on a residual caller under THREE fresh
-- fields and then another lambda. No arbitrary captured-body weakening.
fresh-capture-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (Observed.opaque-program ∷ [])) Observed.fresh-capture-program)
  Observed.fresh-capture-quoted
fresh-capture-path = Replay.ReplayFreshCapture.path environment-scope environment-denotes
open-path : _⇝*_ C.W.sig Observed.open-program Observed.open-quoted
open-path = Replay.ReplayOpen.path
  (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])

-- Positive scoped residual readback is intentionally NOT an admission oracle.
raw-data-not-typing : present (R.verify (Caller.request [] [] [] [] Observed.data-index-program
  (tm-type l0) (r-data [] (Prior.case-recipe ∷ [])) r-leaf)) ≡ false
raw-data-not-typing = refl
raw-neutral-function-not-typing : present (R.verify (Caller.request [] [] [] [] Observed.neutral-function-program
  tm-atom_type (r-app Prior.case-recipe r-leaf) r-leaf)) ≡ false
raw-neutral-function-not-typing = refl
