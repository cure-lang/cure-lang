{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- One checked registry is threaded through recursive data computation.
-- Layout agreement, semantic scope and native typing remain distinct.
------------------------------------------------------------------------
module Proof.RecursiveDataExamples where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l1)
open import Core.NativeRecipe
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (_⇝*_; ⇝*-refl)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.CallerAdmission as Caller
import Core.DataSpine as Layout
import Core.NormalizingAdmission as Admission
import Core.WireChecking as Wire
import Core.NormalFormComparison as Compare
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotation as Model
import Proof.ClosureQuotationExamples as Quotation
import Proof.ClosureQuotationSafety as Safety
open import Proof.CheckedAdmissionExamples using (pick)
import Proof.DataSpineExamples as Source
import Proof.NormalizingAdmissionExamples as AdmissionExample
import Fixtures.ExecutableDataSpine as Registry
import Fixtures.ExecutableRecursiveData as Observed
module C = Source.C
module R = Source.R
module Simulation = Model.Simulation C.W.sig
module Safe = Safety.Safe Source.checked-source
module Checking = Admission.Replay Source.checked-source
module Chars = Wire.Replay Source.checked-source

module Case (depth : ℕ) (program : Term) (env : List E.Value) (value : E.Value) (quoted : Term)
  (evaluated : Previous.result-value (E.run-with C.W.ind 32 program env) ≡ just value)
  (readback : Quotation.term-result (Q.run-with C.W.ind 64 depth value) ≡ just quoted)
  (scoped : present (scope? (length env) program) ≡ true) where
  execution : Q.Normalizes depth env program quoted
  execution = Q.normalized value (Previous.extract (E.run-with C.W.ind 32 program env) value evaluated)
    (Quotation.extract (Q.run-with C.W.ind 64 depth value) quoted readback)
  path : ∀ {terms} → Scope.EnvironmentScoped depth env → Meaning.Environments depth env terms
    → _⇝*_ C.W.sig (substS (Meaning.environment-sub terms) program) quoted
  path scope environment = Simulation.normalization scope
    (pick (scope? (length env) program) scoped) environment execution
  normal : Q.BetaZetaNormal quoted
  normal = Q.quoted-normal (Q.Normalizes.quoted execution)

module CanonicalCase = Case 0 Observed.canonical-program Observed.canonical-environment
  Observed.canonical-value Observed.canonical-quoted refl refl refl
module Nested = Case 0 Observed.nested-program Observed.nested-environment
  Observed.nested-value Observed.nested-quoted refl refl refl
module Domain = Case 0 Observed.domain-program Observed.domain-environment
  Observed.domain-value Observed.domain-quoted refl refl refl
module Body = Case 0 Observed.body-program Observed.body-environment
  Observed.body-value Observed.body-quoted refl refl refl
module Capture = Case 0 Observed.capture-program Observed.capture-environment
  Observed.capture-value Observed.capture-quoted refl refl refl
module Application = Case 0 Observed.application-program Observed.application-environment
  Observed.application-value Observed.application-quoted refl refl refl
module Pi = Case 0 Observed.pi-program Observed.pi-environment
  Observed.pi-value Observed.pi-quoted refl refl refl
module Field = Case 0 Observed.field-program Observed.field-environment
  Observed.field-value Observed.field-quoted refl refl refl
module CaseResult = Case 0 Observed.case-program Observed.case-environment
  Observed.case-value Observed.case-quoted refl refl refl
module Open = Case 1 Observed.open-program Observed.open-environment
  Observed.open-value Observed.open-quoted refl refl refl
source-layout : Layout.SourceLayout C.W.ind "Spine#Indexed"
  (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
source-layout = Layout.source-layout Source.family Source.family-found refl refl
semantic-layout : Layout.SourceLayout C.W.ind "Spine#Indexed"
  (E.v-atom-type ∷ []) (E.v-atom "payload" ∷ [])
semantic-layout = E.evaluated-layout {env = []} source-layout (E.e∷ E.e-atom-type E.e[]) (E.e∷ E.e-atom E.e[])
readback-layout : Layout.SourceLayout C.W.ind "Spine#Indexed"
  (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
readback-layout = Q.quoted-layout {depth = 0} semantic-layout (Q.q∷ Q.q-atom-type Q.q[]) (Q.q∷ Q.q-atom Q.q[])
nested-path : _⇝*_ C.W.sig Observed.nested-program Observed.nested-quoted
nested-path = Nested.path Scope.s[] Meaning.d[]
capture-path : _⇝*_ C.W.sig Observed.capture-program Observed.capture-quoted
capture-path = Capture.path Scope.s[] Meaning.d[]
domain-path : _⇝*_ C.W.sig Observed.domain-program Observed.domain-quoted
domain-path = Domain.path Scope.s[] Meaning.d[]
case-result-path : _⇝*_ C.W.sig Observed.case-program Observed.case-quoted
case-result-path = CaseResult.path Scope.s[] Meaning.d[]
open-path : _⇝*_ C.W.sig Observed.open-program Observed.open-quoted
open-path = Open.path (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])

data-kind : Recipe
data-kind = r-data (r-leaf ∷ []) (r-leaf ∷ [])
return-goal : Term
return-goal = tm-pi unrestricted tm-atom_type (tm-type l1)
identity-goal : Term
identity-goal = tm-pi unrestricted Observed.canonical-program Observed.canonical-program
module Native (program goal : Term) (recipe kind : Recipe)
  (accepted : present (R.verify (Caller.request [] [] [] [] program goal recipe kind)) ≡ true) where
  admitted : R.Checked (Caller.request [] [] [] [] program goal recipe kind)
  admitted = pick (R.verify (Caller.request [] [] [] [] program goal recipe kind)) accepted
module CanonicalNative = Native Observed.canonical-program (tm-type l1) data-kind r-leaf refl
module DomainNative = Native Observed.domain-program identity-goal
  (r-lam data-kind r-leaf) (r-pi data-kind data-kind) refl
module BodyNative = Native Observed.body-program return-goal
  (r-lam r-leaf data-kind) (r-pi r-leaf r-leaf) refl
module CaptureNative = Native Observed.capture-program return-goal
  (r-let r-leaf data-kind (r-lam r-leaf r-leaf)) (r-pi r-leaf r-leaf) refl
module ApplicationNative = Native Observed.application-program (tm-type l1)
  (r-app (r-lam r-leaf r-leaf) data-kind) r-leaf refl
module PiNative = Native Observed.pi-program (tm-type l1) (r-pi data-kind data-kind) r-leaf refl
canonical-safe : C.Sound.SafeState Observed.canonical-quoted (tm-type l1)
canonical-safe = proj₂ (Safe.safe-normalization CanonicalNative.admitted CanonicalCase.execution)
domain-safe : C.Sound.SafeState Observed.domain-quoted identity-goal
domain-safe = proj₂ (Safe.safe-normalization DomainNative.admitted Domain.execution)
body-safe : C.Sound.SafeState Observed.body-quoted return-goal
body-safe = proj₂ (Safe.safe-normalization BodyNative.admitted Body.execution)
capture-safe : C.Sound.SafeState Observed.capture-quoted return-goal
capture-safe = proj₂ (Safe.safe-normalization CaptureNative.admitted Capture.execution)
application-safe : C.Sound.SafeState Observed.application-quoted (tm-type l1)
application-safe = proj₂ (Safe.safe-normalization ApplicationNative.admitted Application.execution)
pi-safe : C.Sound.SafeState Observed.pi-quoted (tm-type l1)
pi-safe = proj₂ (Safe.safe-normalization PiNative.admitted Pi.execution)
safe-run : Quotation.term-result (Safe.run-safe-with 64 DomainNative.admitted) ≡ just Observed.domain-quoted
safe-run = refl

beta-data : Term
beta-data = tm-app (tm-lam unrestricted (tm-type l1) (tm-var 0)) Observed.canonical-program
beta-kind : Recipe
beta-kind = r-app (r-lam r-leaf r-leaf) data-kind
query : Admission.Request
query = Admission.request Observed.domain-program (r-lam data-kind r-leaf) (r-pi data-kind data-kind)
  (tm-pi unrestricted beta-data beta-data) (r-pi beta-kind beta-kind)
encoded : Wire.encode Registry.table query ≡ just Observed.checking-characters
encoded = refl
decoded : Wire.decode Registry.table Observed.checking-characters ≡ just query
decoded = Wire.roundtrip Registry.table query Observed.checking-characters encoded
characters-accepted : Admission.present (Chars.verify 64 Observed.checking-characters) ≡ true
characters-accepted = trans (Chars.verify-decoded 64 Observed.checking-characters query decoded) refl
checked : Checking.Checked query
checked = AdmissionExample.pick (Checking.verify 64 query) refl
original-goal-safe : C.Sound.SafeState Observed.domain-program (Admission.Request.goal query)
original-goal-safe = Checking.Checked.trace-safe checked ⇝*-refl
budgets-agree : ∀ budget → Checking.Checked.run checked budget
  ≡ C.Sound.truncate budget (Checking.Checked.tree checked)
budgets-agree = Checking.Checked.budgets-agree checked
small-checking-budget : Admission.present (Checking.verify 0 query) ≡ false
small-checking-budget = refl
signature-free-comparison : Compare.compare 64 0 [] Observed.canonical-program beta-data
  ≡ Compare.unknown Compare.left-side E.unsupported
signature-free-comparison = refl

fallback-differs : Observed.nested-fallback ≢ Observed.nested-quoted
fallback-differs ()
signature-free-evaluation : E.run 64 Observed.canonical-program [] ≡ E.stop E.unsupported
signature-free-evaluation = refl
signature-free-readback : Q.run 64 0 Observed.canonical-value ≡ E.stop E.unsupported
signature-free-readback = refl
forged-source-rejected : E.run-with C.W.ind 64
  (tm-data "Spine#Indexed" [] (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])) []
  ≡ E.stop (E.data-layout Layout.wrong-parameter-arity)
forged-source-rejected = refl
forged-value-rejected : Q.run-with C.W.ind 64 0
  (E.v-data "Spine#Indexed" [] (E.v-atom-type ∷ E.v-atom "payload" ∷ []))
  ≡ E.stop (E.data-layout Layout.wrong-parameter-arity)
forged-value-rejected = refl
unknown-family : E.run-with C.W.ind 64 (tm-data "Spine#Unknown" [] []) []
  ≡ E.stop (E.data-layout Layout.unknown-family)
unknown-family = refl
wrong-index-count : E.run-with C.W.ind 64 (tm-data "Spine#Indexed" (tm-atom_type ∷ []) []) []
  ≡ E.stop (E.data-layout Layout.wrong-index-arity)
wrong-index-count = refl
changed-registry : Q.run-with (record { families = [] ; builtins = λ _ → nothing }) 64 0 Observed.canonical-value
  ≡ E.stop (E.data-layout Layout.unknown-family)
changed-registry = refl
escaped-nested-field : Q.run-with C.W.ind 64 0
  (E.v-data "Spine#Indexed" (E.v-atom-type ∷ []) (E.v-neutral (E.n-var 0) ∷ []))
  ≡ E.stop E.escaped-level
escaped-nested-field = refl
small-data-budget : E.run-with C.W.ind 1 Observed.canonical-program [] ≡ E.stop E.exhausted
small-data-budget = refl
layout-not-typing : present (R.verify (Caller.request [] [] [] [] Observed.nested-program (tm-type l1)
  (r-data (data-kind ∷ []) (r-leaf ∷ [])) r-leaf)) ≡ false
layout-not-typing = refl
