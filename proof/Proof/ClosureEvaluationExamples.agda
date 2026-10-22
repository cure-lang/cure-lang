{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Actual reviewed Eval/Quote observations are replayed by the MODEL.
-- Positive model traces compose with independently checked native typing.
------------------------------------------------------------------------
module Proof.ClosureEvaluationExamples where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.NativeRecipe
open import Core.Reduction using (_⇝*_; ⇝*-step; ⇝*-refl; β; ξ-lam-body)
import Core.ClosureEval as E
import Core.CallerAdmission as Caller
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationSafety as Safety
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableClosure as Observed
open import Proof.CheckedAdmissionExamples using (pick)
open import Core.CheckedAdmission using (present)
open import Core.Signature using (nothing≠just; just-inj)
module CallerReplay = Caller.Replay Source.Pin.admission
module C = CallerReplay.C
module Simulation = Meaning.Simulation C.W.sig
module Safe = Safety.Safe Source.Pin.admission

result-value : ∀ {A : E.Value → Set} → E.Result (Σ E.Value A) → Maybe E.Value
result-value (E.stop reason) = nothing
result-value (E.done (value , evidence)) = just value
extract : ∀ {A : E.Value → Set} (result : E.Result (Σ E.Value A)) value
  → result-value result ≡ just value → A value
extract (E.stop reason) value ()
extract (E.done (actual , evidence)) value found with just-inj found
... | refl = evidence
module Case (program : Term) (environment : List E.Value) (value : E.Value)
  (observed : result-value (E.run 32 program environment) ≡ just value) where
  evaluated : E.Evaluates environment program value
  evaluated = extract (E.run 32 program environment) value observed

module Beta = Case Observed.beta-program Observed.beta-environment Observed.beta-value refl
module Argument = Case Observed.argument-program Observed.argument-environment Observed.argument-value refl
module Capture = Case Observed.capture-program Observed.capture-environment Observed.capture-value refl
module Higher = Case Observed.higher-program Observed.higher-environment Observed.higher-value refl
module Let = Case Observed.let-program Observed.let-environment Observed.let-value refl
module Domain = Case Observed.domain-program Observed.domain-environment Observed.domain-value refl
module Annotation = Case Observed.annotation-program Observed.annotation-environment Observed.annotation-value refl
module NeutralCase = Case Observed.neutral-program Observed.neutral-environment Observed.neutral-value refl
module Global = Case Observed.global-program Observed.global-environment Observed.global-value refl
module Pi = Case Observed.pi-program Observed.pi-environment Observed.pi-value refl

beta-path : _⇝*_ C.W.sig Observed.beta-program Observed.beta-quoted
beta-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Beta.evaluated))
argument-path : _⇝*_ C.W.sig Observed.argument-program Observed.argument-quoted
argument-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Argument.evaluated))
higher-path : _⇝*_ C.W.sig Observed.higher-program Observed.higher-quoted
higher-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Higher.evaluated))
let-path : _⇝*_ C.W.sig Observed.let-program Observed.let-quoted
let-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Let.evaluated))
domain-path : _⇝*_ C.W.sig Observed.domain-program Observed.domain-quoted
domain-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Domain.evaluated))
pi-path : _⇝*_ C.W.sig Observed.pi-program Observed.pi-quoted
pi-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Pi.evaluated))
global-path : _⇝*_ C.W.sig Observed.global-program Observed.global-quoted
global-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Global.evaluated))

capture-denotation : Term
capture-denotation = tm-lam unrestricted tm-atom_type
  (tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) (tm-atom_lit "payload"))
capture-path : _⇝*_ C.W.sig Observed.capture-program capture-denotation
capture-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Capture.evaluated))
-- Full quotation performs one MORE beta step under the returned binder.
quotation-path : _⇝*_ C.W.sig capture-denotation Observed.capture-quoted
quotation-path = ⇝*-step (ξ-lam-body β) ⇝*-refl
capture-to-quoted : _⇝*_ C.W.sig Observed.capture-program Observed.capture-quoted
capture-to-quoted = Simulation.O.⇝*-trans capture-path quotation-path

module Native (program goal : Term) (body kind : Recipe)
  (accepted : present (CallerReplay.verify (Caller.request [] [] [] [] program goal body kind)) ≡ true) where
  admitted : CallerReplay.Checked (Caller.request [] [] [] [] program goal body kind)
  admitted = pick (CallerReplay.verify (Caller.request [] [] [] [] program goal body kind)) accepted
  safe : ∀ {endpoint} → _⇝*_ C.W.sig (CallerReplay.Checked.closed-subject admitted) endpoint
    → C.Sound.SafeState endpoint (CallerReplay.Checked.closed-goal admitted)
  safe = CallerReplay.Checked.trace-safe admitted

module BetaNative = Native Observed.beta-program Observed.beta-goal (r-app (r-lam r-leaf r-leaf) r-leaf) r-leaf refl
beta-safe : C.Sound.SafeState Observed.beta-quoted Observed.beta-goal
beta-safe = BetaNative.safe beta-path
beta-derived-safe : C.Sound.SafeState Observed.beta-quoted Observed.beta-goal
beta-derived-safe = proj₂ (proj₂ (Safe.safe-evaluation BetaNative.admitted Beta.evaluated))
safe-run-observed : result-value (Safe.run-safe 32 BetaNative.admitted) ≡ just Observed.beta-value
safe-run-observed = refl
module ArgumentNative = Native Observed.argument-program Observed.argument-goal
  (r-app (r-lam r-leaf r-leaf) (r-app (r-lam r-leaf r-leaf) r-leaf)) r-leaf refl
argument-safe : C.Sound.SafeState Observed.argument-quoted Observed.argument-goal
argument-safe = ArgumentNative.safe argument-path
module CaptureNative = Native Observed.capture-program Observed.capture-goal
  (r-app (r-lam r-leaf (r-lam r-leaf (r-app (r-lam r-leaf r-leaf) r-leaf))) r-leaf)
  (r-pi r-leaf r-leaf) refl
capture-safe : C.Sound.SafeState Observed.capture-quoted Observed.capture-goal
capture-safe = CaptureNative.safe capture-to-quoted
module HigherNative = Native Observed.higher-program Observed.higher-goal
  (r-app (r-lam (r-pi r-leaf r-leaf) (r-app r-leaf r-leaf)) (r-lam r-leaf r-leaf)) r-leaf refl
higher-safe : C.Sound.SafeState Observed.higher-quoted Observed.higher-goal
higher-safe = HigherNative.safe higher-path
module LetNative = Native Observed.let-program Observed.let-goal
  (r-let r-leaf (r-app (r-lam r-leaf r-leaf) r-leaf) r-leaf) r-leaf refl
let-safe : C.Sound.SafeState Observed.let-quoted Observed.let-goal
let-safe = LetNative.safe let-path
module DomainNative = Native Observed.domain-program Observed.domain-goal
  (r-convert Observed.domain-goal (c-pi c-zeta c-zeta)
    (r-lam (r-let r-leaf r-leaf r-leaf) r-leaf)) (r-pi r-leaf r-leaf) refl
domain-safe : C.Sound.SafeState Observed.domain-quoted Observed.domain-goal
domain-safe = DomainNative.safe domain-path
module PiNative = Native Observed.pi-program Observed.pi-goal
  (r-pi (r-let r-leaf r-leaf r-leaf) r-leaf) r-leaf refl
pi-safe : C.Sound.SafeState Observed.pi-quoted Observed.pi-goal
pi-safe = PiNative.safe pi-path
module GlobalNative = Native Observed.global-program Observed.global-goal r-leaf r-leaf refl
global-safe : C.Sound.SafeState Observed.global-quoted Observed.global-goal
global-safe = GlobalNative.safe global-path

-- Neutral application has an open, represented environment. It is not
-- promoted to closed admission or certified delta unfolding.
neutral-path : _⇝*_ C.W.sig Observed.neutral-program Observed.neutral-quoted
neutral-path = proj₂ (proj₂ (Simulation.evaluate
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[]) NeutralCase.evaluated))
annotation-path : _⇝*_ C.W.sig Observed.annotation-program Observed.annotation-quoted
annotation-path = proj₂ (proj₂ (Simulation.evaluate {depth = 0} Meaning.d[] Annotation.evaluated))
annotation-not-admitted : present (CallerReplay.verify (Caller.request [] [] [] []
  Observed.annotation-program Observed.annotation-goal (r-let r-leaf r-leaf r-leaf) r-leaf)) ≡ false
annotation-not-admitted = refl

failure : ∀ {A} → E.Result A → Maybe E.Failure
failure (E.done value) = nothing
failure (E.stop reason) = just reason
small-budget : failure (E.run 1 Observed.beta-program []) ≡ just E.exhausted
small-budget = refl
unbound : failure (E.run 4 (tm-var 0) []) ≡ just E.unbound
unbound = refl
non-function : failure (E.run 8 (tm-app tm-atom_type (tm-atom_lit "payload")) []) ≡ just E.non-function
non-function = refl
unsupported : failure (E.run 8 (tm-ctor "Boundary#Pack" []) []) ≡ just E.unsupported
unsupported = refl
omega : Term
omega = tm-app self self
  where self = tm-lam unrestricted tm-atom_type (tm-app (tm-var 0) (tm-var 0))
omega-budget : failure (E.run 16 omega []) ≡ just E.exhausted
omega-budget = refl
wrong-capture : result-value (E.run 32 Observed.capture-program []) ≢
  just (E.v-lam unrestricted E.v-atom-type []
    (tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) (tm-var 1)))
wrong-capture ()
wrong-captured-environment-fails : failure (E.apply 16
  (E.v-lam unrestricted E.v-atom-type []
    (tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) (tm-var 1))) (E.v-atom "payload"))
  ≡ just E.unbound
wrong-captured-environment-fails = refl
unused-omega : Term
unused-omega = tm-app (tm-lam unrestricted tm-atom_type (tm-atom_lit "payload")) omega
unused-argument-still-eager : failure (E.run 16 unused-omega []) ≡ just E.exhausted
unused-argument-still-eager = refl
-- Another specification path can reach a value; exhaustion is not a
-- no-reachable-value theorem or a completeness claim for the strategy.
unused-omega-other-path : _⇝*_ C.W.sig unused-omega (tm-atom_lit "payload")
unused-omega-other-path = ⇝*-step β ⇝*-refl
