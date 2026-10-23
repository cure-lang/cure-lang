{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Actual opening frames and readbacks, independently replayed. Fresh
-- values have scope/denotation, not an asserted native field telescope.
------------------------------------------------------------------------
module Proof.BranchOpeningExamples where

open import Data.Bool using (true)

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; s≤s; z≤n)
open import Data.Maybe using (just)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.CheckedAdmission using (present)
open import Core.NativeRecipe using (scope?)
open import Core.Reduction using (_⇝_; _⇝*_)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.BranchOpening as Opening
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Proof.BranchOpening as Model
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotation as Strong
import Proof.ClosureQuotationExamples as Quotation
import Proof.DataSpineExamples as Source
import Fixtures.ExecutableBranchOpening as Observed
module C = Source.C
module Simulation = Model.Simulation C.W.sig

module Case (depth arity : ℕ) (env opened : List E.Value) (body : Term) (value : E.Value) (quoted : Term)
  (frame : Opening.environment depth arity env ≡ opened)
  (evaluated : Previous.result-value (Opening.run-with C.W.ind 32 depth arity env body) ≡ just value)
  (readback : Quotation.term-result (Q.run-with C.W.ind 64 (arity + depth) value) ≡ just quoted)
  (scoped : present (scope? (length env + arity) body) ≡ true) where
  execution : Q.Normalizes (arity + depth) (Opening.environment depth arity env) body quoted
  execution = Q.normalized value
    (Previous.extract (Opening.run-with C.W.ind 32 depth arity env body) value evaluated)
    (Quotation.extract (Q.run-with C.W.ind 64 (arity + depth) value) quoted readback)
  path : ∀ {captured} → Scope.EnvironmentScoped depth env → Meaning.Environments depth env captured
    → _⇝*_ C.W.sig (substS (extSub^ arity (Meaning.environment-sub captured)) body) quoted
  path scope denoted = Simulation.quotation scope (pick (scope? (length env + arity) body) scoped) denoted execution
  normal : Q.BetaZetaNormal quoted
  normal = Q.quoted-normal (Q.Normalizes.quoted execution)
  scoped-result : Scoped (arity + depth) quoted
  scoped-result = Q.quoted-scoped (Q.Normalizes.quoted execution)

module Zero = Case Observed.zero-depth Observed.zero-arity Observed.zero-environment Observed.zero-opened
  Observed.zero-body Observed.zero-value Observed.zero-quoted refl refl refl refl
module One = Case Observed.one-depth Observed.one-arity Observed.one-environment Observed.one-opened
  Observed.one-body Observed.one-value Observed.one-quoted refl refl refl refl
module First = Case Observed.first-depth Observed.first-arity Observed.first-environment Observed.first-opened
  Observed.first-body Observed.first-value Observed.first-quoted refl refl refl refl
module Last = Case Observed.last-depth Observed.last-arity Observed.last-environment Observed.last-opened
  Observed.last-body Observed.last-value Observed.last-quoted refl refl refl refl
module Outer = Case Observed.outer-depth Observed.outer-arity Observed.outer-environment Observed.outer-opened
  Observed.outer-body Observed.outer-value Observed.outer-quoted refl refl refl refl
module Closure = Case Observed.closure-depth Observed.closure-arity Observed.closure-environment Observed.closure-opened
  Observed.closure-body Observed.closure-value Observed.closure-quoted refl refl refl refl
module Spine = Case Observed.spine-depth Observed.spine-arity Observed.spine-environment Observed.spine-opened
  Observed.spine-body Observed.spine-value Observed.spine-quoted refl refl refl refl
module Redex = Case Observed.redex-depth Observed.redex-arity Observed.redex-environment Observed.redex-opened
  Observed.redex-body Observed.redex-value Observed.redex-quoted refl refl refl refl
module DataCase = Case Observed.data-depth Observed.data-arity Observed.data-environment Observed.data-opened
  Observed.data-body Observed.data-value Observed.data-quoted refl refl refl refl
module Capture = Case Observed.capture-depth Observed.capture-arity Observed.capture-environment Observed.capture-opened
  Observed.capture-body Observed.capture-value Observed.capture-quoted refl refl refl refl
module CaseResult = Case Observed.case-depth Observed.case-arity Observed.case-environment Observed.case-opened
  Observed.case-body Observed.case-value Observed.case-quoted refl refl refl refl

ambient-scope : Scope.EnvironmentScoped 1 (E.v-neutral (E.n-var 0) ∷ [])
ambient-scope = Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[]
ambient-denoted : Meaning.Environments 1 (E.v-neutral (E.n-var 0) ∷ []) (tm-var 0 ∷ [])
ambient-denoted = Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[]
first-path : _⇝*_ C.W.sig (tm-var 2) Observed.first-quoted
first-path = First.path ambient-scope ambient-denoted
last-path : _⇝*_ C.W.sig (tm-var 0) Observed.last-quoted
last-path = Last.path ambient-scope ambient-denoted
outer-path : _⇝*_ C.W.sig (tm-var 3) Observed.outer-quoted
outer-path = Outer.path ambient-scope ambient-denoted
spine-path : _⇝*_ C.W.sig Observed.spine-body Observed.spine-quoted
spine-path = Spine.path ambient-scope ambient-denoted
data-path : _⇝*_ C.W.sig Observed.data-body Observed.data-quoted
data-path = DataCase.path ambient-scope ambient-denoted
case-path : _⇝*_ C.W.sig Observed.case-body Observed.case-quoted
case-path = CaseResult.path ambient-scope ambient-denoted
closure-path : _⇝*_ C.W.sig
  (substS (extSub^ 2 (Meaning.environment-sub (tm-atom_lit "payload" ∷ []))) Observed.closure-body)
  Observed.closure-quoted
closure-path = Closure.path (Scope.s∷ Scope.s-atom Scope.s[]) (Meaning.d∷ Meaning.d-atom Meaning.d[])
captured-data : Term
captured-data = tm-data "Spine#Indexed" (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
capture-path : _⇝*_ C.W.sig
  (substS (extSub^ 1 (Meaning.environment-sub (captured-data ∷ []))) Observed.capture-body)
  Observed.capture-quoted
capture-path = Capture.path
  (Scope.s∷ (Scope.s-data (Scope.s∷ Scope.s-atom-type Scope.s[]) (Scope.s∷ Scope.s-atom Scope.s[])) Scope.s[])
  (Meaning.d∷ (Meaning.d-data (Meaning.d∷ Meaning.d-atom-type Meaning.d[]) (Meaning.d∷ Meaning.d-atom Meaning.d[]))
    Meaning.d[])
redex-path : _⇝*_ C.W.sig Observed.redex-body Observed.redex-quoted
redex-path = Redex.path Scope.s[] Meaning.d[]

wrong-order : Opening.prefix 1 3 ≢ Opening.forward 1 3
wrong-order ()
field-order-distinct : Observed.first-quoted ≢ Observed.last-quoted
field-order-distinct ()
outer-not-field : Observed.outer-quoted ≢ Observed.first-quoted
outer-not-field ()
zero-no-fresh-slot : Opening.environment 0 0 [] ≡ []
zero-no-fresh-slot = refl
zero-unbound : Previous.failure (Opening.run 16 0 0 [] (tm-var 0)) ≡ just E.unbound
zero-unbound = refl
wrong-arity-unbound : Previous.failure (Opening.run 16 0 1 [] (tm-var 1)) ≡ just E.unbound
wrong-arity-unbound = refl
height-budget : Previous.failure (Opening.run-with C.W.ind 0 1 3 Observed.first-environment Observed.first-body)
  ≡ just E.exhausted
height-budget = refl
opening-omega-budget : Previous.failure (Opening.run-with C.W.ind 16 1 3 Observed.first-environment Previous.omega)
  ≡ just E.exhausted
opening-omega-budget = refl
signature-free-data-excluded : Previous.failure (Opening.run 32 1 2 Observed.data-environment Observed.data-body)
  ≡ just E.unsupported
signature-free-data-excluded = refl
outside-frame-equation-false :
  substS (extSub^ 1 (Meaning.environment-sub [])) (tm-var 1)
  ≢ substS (Meaning.environment-sub (Model.terms 1 [])) (tm-var 1)
outside-frame-equation-false ()
outside-frame-not-scoped : Scoped 1 (tm-var 1) → ⊥
outside-frame-not-scoped (sc-var (s≤s ()))
unscoped-caller-not-certified : Scope.EnvironmentScoped 0 (E.v-neutral (E.n-var 0) ∷ []) → ⊥
unscoped-caller-not-certified (Scope.s∷ (Scope.s-neutral (Scope.s-var ())) Scope.s[])

-- Residual syntax is an existing native VALUE, but branch congruence
-- gives it a self-step. This is not a kernel-unsoundness claim.
residual : Term
residual = tm-case (tm-var 0) tm-atom_type []
residual-native-value : Value residual
residual-native-value = neutral (n-case n-var)
residual-self-step : _⇝_ Strong.no-delta residual residual
residual-self-step = Model.case-self-step Strong.no-delta (tm-var 0) tm-atom_type []
not-strong-normal : Q.BetaZetaNormal residual → ⊥
not-strong-normal normal = Strong.normal-no-step normal residual-self-step
strict-residual-irreducibility-impossible :
  (∀ {endpoint} → _⇝_ Strong.no-delta residual endpoint → ⊥) → ⊥
strict-residual-irreducibility-impossible =
  Model.strict-case-irreducibility-impossible Strong.no-delta (tm-var 0) tm-atom_type []
