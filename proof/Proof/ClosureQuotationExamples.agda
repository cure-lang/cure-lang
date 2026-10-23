{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- The modeled readback theorem replaces manual extra reduction steps.
-- Beta/zeta normality is deliberately separated from delta and eta.
------------------------------------------------------------------------
module Proof.ClosureQuotationExamples where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.NativeRecipe
open import Core.Reduction using (_⇝_; _⇝*_; ξ-lam-body; δ)
import Core.ClosureEval as E
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Model
import Proof.ClosureQuotationSafety as Safety
import Proof.ClosureEvaluationExamples as Previous
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableClosure as Old
import Fixtures.ExecutableQuotation as Observed
open import Proof.CheckedAdmissionExamples using (pick)
open import Core.CheckedAdmission using (present)
open import Core.Signature using (just-inj)
module C = Previous.C
module Simulation = Model.Simulation C.W.sig
module Safe = Safety.Safe Source.Pin.admission

term-result : ∀ {A : Term → Set} → E.Result (Σ Term A) → Maybe Term
term-result (E.stop reason) = nothing
term-result (E.done (term , evidence)) = just term
extract : ∀ {A : Term → Set} (result : E.Result (Σ Term A)) term
  → term-result result ≡ just term → A term
extract (E.stop reason) term ()
extract (E.done (actual , evidence)) term found with just-inj found
... | refl = evidence
module Quoted (depth : ℕ) (value : E.Value) (term : Term)
  (observed : term-result (Q.run 64 depth value) ≡ just term) where
  evidence : Q.Quoted depth value term
  evidence = extract (Q.run 64 depth value) term observed
  normal : Q.BetaZetaNormal term
  normal = Q.quoted-normal evidence
  scoped : Scoped depth term
  scoped = Q.quoted-scoped evidence

-- All older observations now have GENERAL modeled Quote evidence.
module OldBeta = Quoted 0 Old.beta-value Old.beta-quoted refl
module OldArgument = Quoted 0 Old.argument-value Old.argument-quoted refl
module OldCapture = Quoted 0 Old.capture-value Old.capture-quoted refl
module OldHigher = Quoted 0 Old.higher-value Old.higher-quoted refl
module OldLet = Quoted 0 Old.let-value Old.let-quoted refl
module OldDomain = Quoted 0 Old.domain-value Old.domain-quoted refl
module OldAnnotation = Quoted 0 Old.annotation-value Old.annotation-quoted refl
module OldNeutral = Quoted 1 Old.neutral-value Old.neutral-quoted refl
module OldGlobal = Quoted 0 Old.global-value Old.global-quoted refl
module OldPi = Quoted 0 Old.pi-value Old.pi-quoted refl
old-capture-execution : Q.Normalizes 0 [] Old.capture-program Old.capture-quoted
old-capture-execution = Q.normalized Old.capture-value Previous.Capture.evaluated OldCapture.evidence
old-capture-derived-safe : C.Sound.SafeState Old.capture-quoted Old.capture-goal
old-capture-derived-safe = proj₂ (Safe.safe-normalization Previous.CaptureNative.admitted old-capture-execution)

module Case (depth : ℕ) (program : Term) (env : List E.Value) (value : E.Value) (term : Term)
  (evaluated : Previous.result-value (E.run 32 program env) ≡ just value)
  (quoted : term-result (Q.run 64 depth value) ≡ just term)
  (scope-ok : present (Core.NativeRecipe.scope? (length env) program) ≡ true) where
  module Eval = Previous.Case program env value evaluated
  module Quote = Quoted depth value term quoted
  execution : Q.Normalizes depth env program term
  execution = Q.normalized value Eval.evaluated Quote.evidence
  path : ∀ {terms} → Scope.EnvironmentScoped depth env → Meaning.Environments depth env terms
    → _⇝*_ C.W.sig (substS (Meaning.environment-sub terms) program) term
  path scope denoted = Simulation.normalization scope
    (pick (Core.NativeRecipe.scope? (length env) program) scope-ok) denoted execution

module Dependent = Case 0 Observed.dependent-program Observed.dependent-environment
  Observed.dependent-value Observed.dependent-quoted refl refl refl
module Argument = Case 1 Observed.argument-program Observed.argument-environment
  Observed.argument-value Observed.argument-quoted refl refl refl
module Domain = Case 0 Observed.domain-program Observed.domain-environment
  Observed.domain-value Observed.domain-quoted refl refl refl
module Global = Case 0 Observed.global-program Observed.global-environment
  Observed.global-value Observed.global-quoted refl refl refl
module Eta = Case 1 Observed.eta-program Observed.eta-environment Observed.eta-value Observed.eta-quoted refl refl refl

module DependentNative = Previous.Native Observed.dependent-program Observed.dependent-goal
  (r-lam r-leaf (r-lam r-leaf (r-app (r-lam r-leaf r-leaf) r-leaf)))
  (r-pi r-leaf (r-pi r-leaf r-leaf)) refl
dependent-safe : C.Sound.SafeState Observed.dependent-quoted Observed.dependent-goal
dependent-safe = proj₂ (Safe.safe-normalization DependentNative.admitted Dependent.execution)
dependent-normalization : term-result (Q.normalise 64 0 Observed.dependent-program []) ≡ just Observed.dependent-quoted
dependent-normalization = refl
safe-run-result : term-result (Safe.run-safe 64 DependentNative.admitted) ≡ just Observed.dependent-quoted
safe-run-result = refl
module DomainNative = Previous.Native Observed.domain-program Observed.domain-goal
  (r-convert Observed.domain-goal
    (c-pi (c-pi c-refl c-zeta) (c-pi c-refl c-zeta))
    (r-lam (r-pi r-leaf (r-let r-leaf r-leaf r-leaf)) r-leaf))
  (r-pi (r-pi r-leaf r-leaf) (r-pi r-leaf r-leaf)) refl
domain-safe : C.Sound.SafeState Observed.domain-quoted Observed.domain-goal
domain-safe = proj₂ (Safe.safe-normalization DomainNative.admitted Domain.execution)
module GlobalNative = Previous.Native Observed.global-program Observed.global-goal
  (r-lam r-leaf r-leaf) (r-pi r-leaf r-leaf) refl
global-safe : C.Sound.SafeState Observed.global-quoted Observed.global-goal
global-safe = proj₂ (Safe.safe-normalization GlobalNative.admitted Global.execution)
global-beta-zeta-normal : Q.BetaZetaNormal Observed.global-quoted
global-beta-zeta-normal = Global.Quote.normal
global-still-steps : _⇝_ C.W.sig Observed.global-quoted
  (tm-lam unrestricted tm-atom_type (tm-atom_lit "answer"))
global-still-steps = ξ-lam-body (δ refl)
argument-path : _⇝*_ C.W.sig Observed.argument-program Observed.argument-quoted
argument-path = Argument.path
  (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])
eta-path : _⇝*_ C.W.sig Observed.eta-program Observed.eta-quoted
eta-path = Eta.path
  (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])
eta-not-contracted : Observed.eta-quoted ≢ tm-var 0
eta-not-contracted ()

failure : ∀ {A} → E.Result A → Maybe E.Failure
failure (E.done result) = nothing
failure (E.stop reason) = just reason
escaped-readback : failure (Q.run 8 0 (E.v-neutral (E.n-var 0))) ≡ just E.escaped-level
escaped-readback = refl
small-quote-budget : failure (Q.run 1 0 Old.capture-value) ≡ just E.exhausted
small-quote-budget = refl
latent-omega : E.Value
latent-omega = E.v-lam unrestricted E.v-atom-type [] Previous.omega
latent-evaluation-succeeds : Previous.result-value
  (E.run 4 (tm-lam unrestricted tm-atom_type Previous.omega) []) ≡ just latent-omega
latent-evaluation-succeeds = refl
latent-quote-exhausts : failure (Q.run 16 0 latent-omega) ≡ just E.exhausted
latent-quote-exhausts = refl
malformed-capture : E.Value
malformed-capture = E.v-lam unrestricted E.v-atom-type [] (tm-var 1)
malformed-quote-fails : failure (Q.run 16 0 malformed-capture) ≡ just E.unbound
malformed-quote-fails = refl
malformed-scope-impossible : Scope.ValueScoped 0 malformed-capture → ⊥
malformed-scope-impossible (Scope.s-lam domain Scope.s[] (sc-var (s≤s ())))
raw-denotation : Meaning.Denotes 0 malformed-capture (tm-lam unrestricted tm-atom_type (tm-var 1))
raw-denotation = Meaning.d-lam Meaning.d-atom-type Meaning.d[]
raw-denotation-not-weakening : rename wk (tm-lam unrestricted tm-atom_type (tm-var 1))
  ≢ tm-lam unrestricted tm-atom_type (tm-var 1)
raw-denotation-not-weakening ()
