{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Recursive constructor MODEL refinement and actual fixed observations.
-- Family splitting, compact constructors and recursive cases stay separate.
------------------------------------------------------------------------
module Proof.ConstructorEvaluationExamples where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (s≤s; z≤n)
open import Data.Fin using (suc; zero)
open import Data.Empty using (⊥)
open import Data.Product using (proj₂)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.NativeRecipe
open import Core.Typing using (Conversion)
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick)
open import Core.Reduction using (_⇝_; _⇝*_; ξ-ctor-at; δ)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.NormalFormComparison as Compare
import Core.CallerAdmission as Caller
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotation as Model
import Proof.ClosureQuotationExamples as Quotation
import Proof.ClosureQuotationSafety as Safety
import Proof.ClosureCaseExamples as Cases
import Proof.WireSnapshotExamples as Source
import Proof.NativeCertificateExamples as Existing
import Proof.NormalFormComparisonExamples as Comparison
import Fixtures.ExecutableConstructor as Observed
module C = Previous.C
module Safe = Safety.Safe Source.Pin.admission

module Packed = Quotation.Case 0 Observed.packed-program Observed.packed-environment
  Observed.packed-value Observed.packed-quoted refl refl refl
module Redex = Quotation.Case 0 Observed.redex-program Observed.redex-environment
  Observed.redex-value Observed.redex-quoted refl refl refl
module Nested = Quotation.Case 0 Observed.nested-program Observed.nested-environment
  Observed.nested-value Observed.nested-quoted refl refl refl
module FieldClosure = Quotation.Case 0 Observed.field-closure-program Observed.field-closure-environment
  Observed.field-closure-value Observed.field-closure-quoted refl refl refl
module Captured = Quotation.Case 0 Observed.captured-program Observed.captured-environment
  Observed.captured-value Observed.captured-quoted refl refl refl
module UnderBinder = Quotation.Case 0 Observed.under-binder-program Observed.under-binder-environment
  Observed.under-binder-value Observed.under-binder-quoted refl refl refl
module Open = Quotation.Case 1 Observed.open-program Observed.open-environment
  Observed.open-value Observed.open-quoted refl refl refl
module GlobalField = Quotation.Case 0 Observed.global-field-program Observed.global-field-environment
  Observed.global-field-value Observed.global-field-quoted refl refl refl
module CaseTree = Cases.Observation Observed.case-tree-program Observed.case-tree-environment
  Observed.case-tree-value Observed.case-tree-quoted refl refl refl
module CaseField = Cases.Observation Observed.case-field-program Observed.case-field-environment
  Observed.case-field-value Observed.case-field-quoted refl refl refl

nested-path : _⇝*_ C.W.sig Observed.nested-program Observed.nested-quoted
nested-path = Nested.path Scope.s[] Meaning.d[]
closure-field-path : _⇝*_ C.W.sig Observed.field-closure-program Observed.field-closure-quoted
closure-field-path = FieldClosure.path Scope.s[] Meaning.d[]
captured-path : _⇝*_ C.W.sig Observed.captured-program Observed.captured-quoted
captured-path = Captured.path Scope.s[] Meaning.d[]
under-binder-path : _⇝*_ C.W.sig Observed.under-binder-program Observed.under-binder-quoted
under-binder-path = UnderBinder.path Scope.s[] Meaning.d[]
open-path : _⇝*_ C.W.sig Observed.open-program Observed.open-quoted
open-path = Open.path (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])
case-tree-path : _⇝*_ C.W.sig Observed.case-tree-program Observed.case-tree-quoted
case-tree-path = CaseTree.path Scope.s[] Meaning.d[]
case-field-path : _⇝*_ C.W.sig Observed.case-field-program Observed.case-field-quoted
case-field-path = CaseField.path Scope.s[] Meaning.d[]

data-kind : Recipe
data-kind = r-data [] (r-leaf ∷ [])
ctor-recipe : Recipe
ctor-recipe = r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])
function-goal : Term
function-goal = tm-pi unrestricted tm-atom_type Existing.goal
function-kind : Recipe
function-kind = r-pi r-leaf data-kind

module PackedNative = Previous.Native Observed.packed-program Existing.goal ctor-recipe data-kind refl
packed-safe : C.Sound.SafeState Observed.packed-quoted Existing.goal
packed-safe = proj₂ (Safe.safe-normalization PackedNative.admitted Packed.execution)
module RedexNative = Previous.Native Observed.redex-program Existing.goal
  (r-ctor [] [] (r-leaf ∷ r-let r-leaf (r-app (r-lam r-leaf r-leaf) r-leaf) r-leaf ∷ [])) data-kind refl
redex-safe : C.Sound.SafeState Observed.redex-quoted Existing.goal
redex-safe = proj₂ (Safe.safe-normalization RedexNative.admitted Redex.execution)
module CapturedNative = Previous.Native Observed.captured-program function-goal
  (r-let data-kind ctor-recipe (r-lam r-leaf r-leaf)) function-kind refl
captured-safe : C.Sound.SafeState Observed.captured-quoted function-goal
captured-safe = proj₂ (Safe.safe-normalization CapturedNative.admitted Captured.execution)
module UnderBinderNative = Previous.Native Observed.under-binder-program function-goal
  (r-lam r-leaf ctor-recipe) function-kind refl
under-binder-safe : C.Sound.SafeState Observed.under-binder-quoted function-goal
under-binder-safe = proj₂ (Safe.safe-normalization UnderBinderNative.admitted UnderBinder.execution)
module GlobalFieldNative = Previous.Native Observed.global-field-program Existing.goal ctor-recipe data-kind refl
global-field-safe : C.Sound.SafeState Observed.global-field-quoted Existing.goal
global-field-safe = proj₂ (Safe.safe-normalization GlobalFieldNative.admitted GlobalField.execution)

-- Readback recursively normalizes fields, including closure bodies.
nested-irreducible : ∀ {endpoint} → _⇝_ Model.no-delta Observed.nested-quoted endpoint → ⊥
nested-irreducible = Model.normal-no-step Nested.Quote.normal
closure-field-irreducible : ∀ {endpoint} → _⇝_ Model.no-delta Observed.field-closure-quoted endpoint → ⊥
closure-field-irreducible = Model.normal-no-step FieldClosure.Quote.normal
-- No-delta is essential even for an ordinary constructor's later field.
global-field-still-steps : _⇝_ C.W.sig Observed.global-field-quoted
  (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "answer" ∷ []))
global-field-still-steps = ξ-ctor-at (suc zero) (δ refl)
field-normalized-comparison : Compare.classify
  (Compare.compare 64 0 [] Observed.redex-program Observed.packed-program) ≡ Compare.equal-forms
field-normalized-comparison = refl
module EqualFields = Comparison.Equal 0 [] Observed.redex-program Observed.packed-program refl
field-converts : Conversion._≈_ C.W.M.conversion Observed.redex-program Observed.packed-program
field-converts = Comparison.Sound.closed-conversion
  (pick (scope? 0 Observed.redex-program) refl) (pick (scope? 0 Observed.packed-program) refl) EqualFields.evidence
constructor-names-distinct : Compare.classify (Compare.compare 64 0 []
  (tm-ctor "Boundary#Pack" []) (tm-ctor "Boundary#Alternate" [])) ≡ Compare.distinct-forms
constructor-names-distinct = refl
constructor-fields-distinct : Compare.classify (Compare.compare 64 0 []
  (tm-ctor "Boundary#Pack" (tm-atom_type ∷ []))
  (tm-ctor "Boundary#Pack" (tm-atom_lit "payload" ∷ []))) ≡ Compare.distinct-forms
constructor-fields-distinct = refl

-- Generic MODEL constructors do not claim actual compact-Bounded identity.
module CompactModel = Quotation.Case 0 Observed.compact-program []
  (E.v-ctor "First" (E.v-atom-type ∷ [])) Observed.compact-program refl refl refl
actual-compacts : Observed.compact-actual-quoted ≡ tm-bounded_lit 0
actual-compacts = refl
compact-not-generic : Observed.compact-actual-quoted ≢ Observed.compact-program
compact-not-generic ()
-- Data-family readback needs a metadata-dependent split, not vctor recursion.
actual-flat-split-differ : Observed.data-flat-quoted ≢ Observed.data-split-quoted
actual-flat-split-differ ()
actual-signature-split : Observed.data-split-quoted ≡ Observed.data-program
actual-signature-split = refl
data-remains-unsupported : Previous.failure (E.run 32 Observed.data-program []) ≡ just E.unsupported
data-remains-unsupported = refl

empty-ctor-positive : Previous.result-value (E.run 8 (tm-ctor "Boundary#Pack" []) [])
  ≡ just (E.v-ctor "Boundary#Pack" [])
empty-ctor-positive = refl
empty-ctor-not-admitted : present (Previous.CallerReplay.verify
  (Caller.request [] [] [] [] (tm-ctor "Boundary#Pack" []) Existing.goal
    (r-ctor [] [] []) data-kind)) ≡ false
empty-ctor-not-admitted = refl
ctor-not-function : Previous.failure (E.apply 8 Observed.packed-value (E.v-atom "payload")) ≡ just E.non-function
ctor-not-function = refl
small-evaluation-budget : Previous.failure (E.run 1 Observed.nested-program []) ≡ just E.exhausted
small-evaluation-budget = refl
small-quotation-budget : Quotation.failure (Q.run 1 0 Observed.nested-value) ≡ just E.exhausted
small-quotation-budget = refl
unbound-later-field : Previous.failure (E.run 16
  (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-var 0 ∷ [])) []) ≡ just E.unbound
unbound-later-field = refl
unsupported-later-field : Previous.failure (E.run 16
  (tm-ctor "Boundary#Pack" (tm-atom_type ∷ Observed.data-program ∷ [])) []) ≡ just E.unsupported
unsupported-later-field = refl
escaped-nested-level : Quotation.failure (Q.run 16 0
  (E.v-ctor "Boundary#Pack" (E.v-ctor "Boundary#Alternate" (E.v-neutral (E.n-var 0) ∷ []) ∷ [])))
  ≡ just E.escaped-level
escaped-nested-level = refl
unscoped-latent-field : E.Value
unscoped-latent-field = E.v-ctor "Boundary#Pack"
  (E.v-lam unrestricted E.v-atom-type [] (tm-var 1) ∷ [])
unscoped-latent-readback : Quotation.failure (Q.run 32 0 unscoped-latent-field) ≡ just E.unbound
unscoped-latent-readback = refl
unscoped-latent-rejected : Scope.ValueScoped 0 unscoped-latent-field → ⊥
unscoped-latent-rejected
  (Scope.s-ctor (Scope.s∷ (Scope.s-lam domain Scope.s[] (sc-var (s≤s ()))) Scope.s[]))
latent-omega-evaluates : Previous.result-value (E.run 16
  (tm-ctor "Boundary#Pack" (tm-lam unrestricted tm-atom_type Previous.omega ∷ [])) [])
  ≡ just (E.v-ctor "Boundary#Pack" (Quotation.latent-omega ∷ []))
latent-omega-evaluates = refl
latent-omega-quotation-exhausts : Quotation.failure
  (Q.run 16 0 (E.v-ctor "Boundary#Pack" (Quotation.latent-omega ∷ []))) ≡ just E.exhausted
latent-omega-quotation-exhausts = refl
eager-omega-field : Previous.failure (E.run 16
  (tm-ctor "Boundary#Pack" (Previous.omega ∷ [])) []) ≡ just E.exhausted
eager-omega-field = refl
