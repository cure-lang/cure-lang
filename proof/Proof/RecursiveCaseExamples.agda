{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Shared recursive cases, scoped readback and original-goal admission.
-- Fixed implementation observations remain separate from universal refinement.
------------------------------------------------------------------------
module Proof.RecursiveCaseExamples where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.NativeRecipe
open import Core.Reduction using (_⇝*_; ⇝*-refl)
open import Core.CheckedAdmission using (present)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.NormalFormComparison as Compare
import Core.NormalizingAdmission as Admission
import Core.CallerAdmission as Caller
import Core.DependentTyping as Native
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotationExamples as Quotation
import Proof.ClosureQuotationSafety as Safety
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as Existing
import Proof.EvaluatedCaseExamples as Earlier
import Proof.NormalizingAdmissionExamples as AdmissionExample
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableRecursiveCase as Observed
module C = Previous.C
module Safe = Safety.Safe Source.Pin.admission
module R = Admission.Replay Source.Pin.admission

module Unpack = Quotation.Case 0 Observed.unpack-program Observed.unpack-environment
  Observed.unpack-value Observed.unpack-quoted refl refl refl
module Scrutinee = Quotation.Case 0 Observed.scrutinee-program Observed.scrutinee-environment
  Observed.scrutinee-value Observed.scrutinee-quoted refl refl refl
module Body = Quotation.Case 0 Observed.body-program Observed.body-environment
  Observed.body-value Observed.body-quoted refl refl refl
module Application = Quotation.Case 0 Observed.application-program Observed.application-environment
  Observed.application-value Observed.application-quoted refl refl refl
module Field = Quotation.Case 0 Observed.field-program Observed.field-environment
  Observed.field-value Observed.field-quoted refl refl refl
module Lambda = Quotation.Case 0 Observed.lambda-program Observed.lambda-environment
  Observed.lambda-value Observed.lambda-quoted refl refl refl
module Pi = Quotation.Case 0 Observed.pi-program Observed.pi-environment
  Observed.pi-value Observed.pi-quoted refl refl refl
module TypeCase = Quotation.Case 0 Observed.type-program Observed.type-environment
  Observed.type-value Observed.type-quoted refl refl refl
module Capture = Quotation.Case 0 Observed.capture-program Observed.capture-environment
  Observed.capture-value Observed.capture-quoted refl refl refl
module Outer = Quotation.Case 0 Observed.outer-program Observed.outer-environment
  Observed.outer-value Observed.outer-quoted refl refl refl

scrutinee-path : _⇝*_ C.W.sig Observed.scrutinee-program Observed.scrutinee-quoted
scrutinee-path = Scrutinee.path Scope.s[] Meaning.d[]
body-path : _⇝*_ C.W.sig Observed.body-program Observed.body-quoted
body-path = Body.path Scope.s[] Meaning.d[]
lambda-path : _⇝*_ C.W.sig Observed.lambda-program Observed.lambda-quoted
lambda-path = Lambda.path Scope.s[] Meaning.d[]
capture-path : _⇝*_ C.W.sig Observed.capture-program Observed.capture-quoted
capture-path = Capture.path Scope.s[] Meaning.d[]
outer-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (tm-atom_lit "hidden" ∷ [])) Observed.outer-program) Observed.outer-quoted
outer-path = Outer.path (Scope.s∷ Scope.s-atom Scope.s[]) (Meaning.d∷ Meaning.d-atom Meaning.d[])

unpack-recipe : Recipe
unpack-recipe = r-convert tm-atom_type Recipes.unpack-conversion Recipes.unpack-case-recipe
module UnpackNative = Previous.Native Observed.unpack-program tm-atom_type unpack-recipe r-leaf refl
module ApplicationNative = Previous.Native Observed.application-program tm-atom_type
  (r-app (r-lam r-leaf r-leaf) unpack-recipe) r-leaf refl
module FieldNative = Previous.Native Observed.field-program Existing.goal
  (r-ctor [] [] (r-leaf ∷ unpack-recipe ∷ [])) Earlier.data-kind refl
unpack-safe : C.Sound.SafeState Observed.unpack-quoted tm-atom_type
unpack-safe = proj₂ (Safe.safe-normalization UnpackNative.admitted Unpack.execution)
application-safe : C.Sound.SafeState Observed.application-quoted tm-atom_type
application-safe = proj₂ (Safe.safe-normalization ApplicationNative.admitted Application.execution)
field-safe : C.Sound.SafeState Observed.field-quoted Existing.goal
field-safe = proj₂ (Safe.safe-normalization FieldNative.admitted Field.execution)

type-motive : Term
type-motive = tm-lam unrestricted (tm-type l0)
  (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-type l0))
branch-middle : Name → Term → Term
branch-middle name index = tm-app
  (tm-lam unrestricted (tm-data "Boundary#Packed" [] (index ∷ [])) (tm-type l0))
  (tm-ctor name (tm-var 1 ∷ tm-var 0 ∷ []))
branch-conversion : Name → Term → ConvRecipe
branch-conversion name index = c-sym (c-trans (branch-middle name index) (c-app c-beta c-refl) c-beta)
type-case-recipe : Recipe
type-case-recipe = r-case Earlier.ctor-recipe [] (r-leaf ∷ []) l1
  Recipes.case-kind-recipe Recipes.case-motive-recipe
  ((Recipes.case-field-recipes ,
      r-convert (Native.branchGoal "Boundary#Pack" [] Existing.pack type-motive)
        (branch-conversion "Boundary#Pack" (tm-var 1)) r-leaf) ∷
   (Recipes.case-field-recipes ,
      r-convert (Native.branchGoal "Boundary#Alternate" [] Existing.alternate type-motive)
        (branch-conversion "Boundary#Alternate" Recipes.alternate-index) r-leaf) ∷ [])
type-kind : Recipe
type-kind = r-convert (tm-type l0)
  (c-trans (tm-app
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])) (tm-type l0)) Earlier.packed)
    (c-app c-beta c-refl) c-beta) type-case-recipe
module TypeNative = Previous.Native Observed.type-program (tm-type l0) type-kind r-leaf refl
module PiNative = Previous.Native Observed.pi-program (tm-type l0) (r-pi type-kind r-leaf) r-leaf refl
type-safe : C.Sound.SafeState Observed.type-quoted (tm-type l0)
type-safe = proj₂ (Safe.safe-normalization TypeNative.admitted TypeCase.execution)
pi-safe : C.Sound.SafeState Observed.pi-quoted (tm-type l0)
pi-safe = proj₂ (Safe.safe-normalization PiNative.admitted Pi.execution)

type-comparison : Compare.classify (Compare.compare 64 0 [] tm-atom_type Observed.type-program)
  ≡ Compare.equal-forms
type-comparison = refl
-- No iota conversion path is supplied to admission. It is derived from
-- bounded evaluation/readback AFTER actual synthesis and both kind guards.
query : Admission.Request
query = Admission.request (tm-atom_lit "payload") r-leaf r-leaf Observed.type-program type-kind
checked : R.Checked query
checked = AdmissionExample.pick (R.verify 64 query) refl
original-case-goal-safe : C.Sound.SafeState (tm-atom_lit "payload") Observed.type-program
original-case-goal-safe = R.Checked.trace-safe checked ⇝*-refl
budgets-agree : ∀ budget → R.Checked.run checked budget
  ≡ C.Sound.truncate budget (R.Checked.tree checked)
budgets-agree = R.Checked.budgets-agree checked
small-admission-budget : Admission.present (R.verify 0 query) ≡ false
small-admission-budget = refl

latent-neutral : E.Value
latent-neutral = E.v-lam unrestricted E.v-atom-type []
  (tm-case (tm-var 0) tm-atom_type (("Boundary#Pack" , 2 , tm-var 0) ∷ []))
latent-neutral-evaluates : Previous.result-value (E.run 32 Observed.latent-neutral-program []) ≡ just latent-neutral
latent-neutral-evaluates = refl
latent-neutral-readback-stops : Quotation.failure (Q.run 64 0 latent-neutral) ≡ just E.neutral-scrutinee
latent-neutral-readback-stops = refl
actual-neutral-readback-succeeds : Observed.latent-neutral-actual-quoted ≡ Observed.latent-neutral-program
actual-neutral-readback-succeeds = refl
-- Shared execution broadens; the separate native recipe protocol still
-- does NOT reconstruct case contexts in a nonempty ambient caller.
nonempty-case-replay-still-excluded : present (Previous.CallerReplay.verify
  (Caller.request [] [] [] [] Observed.lambda-program (tm-pi unrestricted tm-atom_type tm-atom_type)
    (r-lam r-leaf (Earlier.native-recipe
      (tm-case (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-var 0 ∷ [])) Existing.motive-term Existing.branches)
      Earlier.ctor-recipe)) (r-pi r-leaf r-leaf))) ≡ false
nonempty-case-replay-still-excluded = refl

raw-case : Term → Term
raw-case body = tm-case (tm-ctor "Boundary#Pack" []) tm-atom_type (("Boundary#Pack" , 0 , body) ∷ [])
missing-branch : Previous.failure (E.run 16 (tm-case (tm-ctor "Boundary#Pack" []) tm-atom_type []) [])
  ≡ just E.missing-branch
missing-branch = refl
wrong-first-arity : Previous.failure (E.run 16 (tm-case (tm-ctor "Boundary#Pack" []) tm-atom_type
  (("Boundary#Pack" , 1 , tm-atom_type) ∷ ("Boundary#Pack" , 0 , tm-atom_type) ∷ [])) [])
  ≡ just E.arity-mismatch
wrong-first-arity = refl
non-constructor : Previous.failure (E.run 16 (tm-case tm-atom_type tm-atom_type []) []) ≡ just E.non-constructor
non-constructor = refl
unsupported-data : Previous.failure (E.run 16
  (tm-case (tm-data "Boundary#Packed" [] []) tm-atom_type []) []) ≡ just E.unsupported
unsupported-data = refl
unbound-body : Previous.failure (E.run 16 (raw-case (tm-var 0)) []) ≡ just E.unbound
unbound-body = refl
small-case-budget : Previous.failure (E.run 1 Observed.unpack-program []) ≡ just E.exhausted
small-case-budget = refl
nested-omega-budget : Previous.failure (E.run 16 (raw-case (raw-case Previous.omega)) []) ≡ just E.exhausted
nested-omega-budget = refl
unsupported-compact : Previous.failure (E.run 16 (tm-case (tm-nat_lit 0) tm-atom_type []) []) ≡ just E.unsupported
unsupported-compact = refl
