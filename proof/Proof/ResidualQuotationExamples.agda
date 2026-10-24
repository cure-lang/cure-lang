{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Actual finite observations have positive MODEL evaluation/readback.
-- Raw successes are not typing; native admission is checked separately.
------------------------------------------------------------------------
module Proof.ResidualQuotationExamples where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.NativeRecipe using (scope?)
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (_⇝*_)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.DataSpine as Layout
import Core.ResidualNormal as Normal
import Proof.ResidualNormal as Residual
import Proof.ResidualQuotation as Model
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quote
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotationExamples as OldQuote
import Fixtures.ExecutableResidualQuotation as Observed
module C = Previous.C
module Simulation = Quote.Simulation C.W.sig

module Observation (depth : ℕ) (env : List E.Value) (program : Term) (value : E.Value) (quoted : Term)
  (accepted : OldQuote.term-result (Q.normalise-residual-with C.W.ind 64 depth program env) ≡ just quoted)
  (same-value : Q.ResidualNormalizes.value
    (OldQuote.extract (Q.normalise-residual-with C.W.ind 64 depth program env) quoted accepted) ≡ value)
  (scope-ok : present (scope? (length env) program) ≡ true) where
  execution : Q.ResidualNormalizes depth env program quoted
  execution = OldQuote.extract (Q.normalise-residual-with C.W.ind 64 depth program env) quoted accepted
  source-scope : Scoped (length env) program
  source-scope = pick (scope? (length env) program) scope-ok
  scoped : Scoped depth quoted
  scoped = Q.quoted-scoped (Q.ResidualNormalizes.quoted execution)
  normal : Normal.Normal Residual.no-delta quoted
  normal = Model.normal (Q.ResidualNormalizes.quoted execution)
  value-scoped : Scope.EnvironmentScoped depth env → Scope.ValueScoped depth value
  value-scoped scope = subst (Scope.ValueScoped depth) same-value
    (Scope.evaluate-scoped scope source-scope (Q.ResidualNormalizes.evaluated execution))
  path : ∀ {captured} → Scope.EnvironmentScoped depth env → Meaning.Environments depth env captured
    → _⇝*_ C.W.sig (substS (Meaning.environment-sub captured) program) quoted
  path scope env = Simulation.residual-normalization scope source-scope env execution

-- Reviewed observation instances.

module ReplayOpaque = Observation Observed.opaque-depth Observed.opaque-environment
  Observed.opaque-program Observed.opaque-value Observed.opaque-quoted refl refl refl
module ReplayBranch = Observation Observed.branch-depth Observed.branch-environment
  Observed.branch-program Observed.branch-value Observed.branch-quoted refl refl refl
module ReplayMotive = Observation Observed.motive-depth Observed.motive-environment
  Observed.motive-program Observed.motive-value Observed.motive-quoted refl refl refl
module ReplayScrutinee = Observation Observed.scrutinee-depth Observed.scrutinee-environment
  Observed.scrutinee-program Observed.scrutinee-value Observed.scrutinee-quoted refl refl refl
module ReplayOpen = Observation Observed.open-depth Observed.open-environment
  Observed.open-program Observed.open-value Observed.open-quoted refl refl refl
module ReplaySpine = Observation Observed.spine-depth Observed.spine-environment
  Observed.spine-program Observed.spine-value Observed.spine-quoted refl refl refl
module ReplayZero = Observation Observed.zero-depth Observed.zero-environment
  Observed.zero-program Observed.zero-value Observed.zero-quoted refl refl refl
module ReplayMulti = Observation Observed.multi-depth Observed.multi-environment
  Observed.multi-program Observed.multi-value Observed.multi-quoted refl refl refl
module ReplayCapture = Observation Observed.capture-depth Observed.capture-environment
  Observed.capture-program Observed.capture-value Observed.capture-quoted refl refl refl
module ReplayData = Observation Observed.data-depth Observed.data-environment
  Observed.data-program Observed.data-value Observed.data-quoted refl refl refl
module ReplaySharedCase = Observation Observed.shared-case-depth Observed.shared-case-environment
  Observed.shared-case-program Observed.shared-case-value Observed.shared-case-quoted refl refl refl
module ReplayDelta = Observation Observed.delta-depth Observed.delta-environment
  Observed.delta-program Observed.delta-value Observed.delta-quoted refl refl refl
module ReplayNestedScrutinee = Observation Observed.nested-scrutinee-depth Observed.nested-scrutinee-environment
  Observed.nested-scrutinee-program Observed.nested-scrutinee-value Observed.nested-scrutinee-quoted refl refl refl
module ReplayNestedBranch = Observation Observed.nested-branch-depth Observed.nested-branch-environment
  Observed.nested-branch-program Observed.nested-branch-value Observed.nested-branch-quoted refl refl refl
module ReplayLamBody = Observation Observed.lam-body-depth Observed.lam-body-environment
  Observed.lam-body-program Observed.lam-body-value Observed.lam-body-quoted refl refl refl
module ReplayLamDomain = Observation Observed.lam-domain-depth Observed.lam-domain-environment
  Observed.lam-domain-program Observed.lam-domain-value Observed.lam-domain-quoted refl refl refl
module ReplayPiBody = Observation Observed.pi-body-depth Observed.pi-body-environment
  Observed.pi-body-program Observed.pi-body-value Observed.pi-body-quoted refl refl refl
module ReplayCtorField = Observation Observed.ctor-field-depth Observed.ctor-field-environment
  Observed.ctor-field-program Observed.ctor-field-value Observed.ctor-field-quoted refl refl refl
module ReplayDataIndex = Observation Observed.data-index-depth Observed.data-index-environment
  Observed.data-index-program Observed.data-index-value Observed.data-index-quoted refl refl refl
module ReplayNeutralFunction = Observation Observed.neutral-function-depth Observed.neutral-function-environment
  Observed.neutral-function-program Observed.neutral-function-value Observed.neutral-function-quoted refl refl refl
module ReplayNeutralArgument = Observation Observed.neutral-argument-depth Observed.neutral-argument-environment
  Observed.neutral-argument-program Observed.neutral-argument-value Observed.neutral-argument-quoted refl refl refl
module ReplayBetaArgument = Observation Observed.beta-argument-depth Observed.beta-argument-environment
  Observed.beta-argument-program Observed.beta-argument-value Observed.beta-argument-quoted refl refl refl
module ReplayLetCapture = Observation Observed.let-capture-depth Observed.let-capture-environment
  Observed.let-capture-program Observed.let-capture-value Observed.let-capture-quoted refl refl refl
module ReplayEnvironment = Observation Observed.environment-depth Observed.environment-environment
  Observed.environment-program Observed.environment-value Observed.environment-quoted refl refl refl
module ReplayFreshCapture = Observation Observed.fresh-capture-depth Observed.fresh-capture-environment
  Observed.fresh-capture-program Observed.fresh-capture-value Observed.fresh-capture-quoted refl refl refl
module ReplayExactCase = Observation Observed.exact-case-depth Observed.exact-case-environment
  Observed.exact-case-program Observed.exact-case-value Observed.exact-case-quoted refl refl refl
module ReplayNestedMotive = Observation Observed.nested-motive-depth Observed.nested-motive-environment
  Observed.nested-motive-program Observed.nested-motive-value Observed.nested-motive-quoted refl refl refl
module ReplayBranchBinder = Observation Observed.branch-binder-depth Observed.branch-binder-environment
  Observed.branch-binder-program Observed.branch-binder-value Observed.branch-binder-quoted refl refl refl
module ReplayTriple = Observation Observed.triple-depth Observed.triple-environment
  Observed.triple-program Observed.triple-value Observed.triple-quoted refl refl refl
module ReplayTypedScrutinee = Observation Observed.typed-scrutinee-depth Observed.typed-scrutinee-environment
  Observed.typed-scrutinee-program Observed.typed-scrutinee-value Observed.typed-scrutinee-quoted refl refl refl
module ReplayTypedBranch = Observation Observed.typed-branch-depth Observed.typed-branch-environment
  Observed.typed-branch-program Observed.typed-branch-value Observed.typed-branch-quoted refl refl refl

-- Controls: compatibility remains strict and finite budgets are not divergence.
strict-evaluator-still-rejects : Previous.failure (E.run-with C.W.ind 64 Observed.opaque-program []) ≡ just E.neutral-scrutinee
strict-evaluator-still-rejects = refl
strict-readback-still-rejects : Previous.failure (Q.run 64 0 Observed.opaque-value) ≡ just E.neutral-scrutinee
strict-readback-still-rejects = refl
strict-normalizer-still-rejects : Previous.failure (Q.normalise-with C.W.ind 64 0 Observed.nested-scrutinee-program [])
  ≡ just E.neutral-scrutinee
strict-normalizer-still-rejects = refl
no-budget : Previous.failure (Q.normalise-residual-with C.W.ind 0 0 Observed.opaque-program []) ≡ just E.exhausted
no-budget = refl
escaped-head : Previous.failure (Q.normalise-residual-with C.W.ind 64 0
  (tm-case (tm-var 0) tm-atom_type []) (E.v-neutral (E.n-var 0) ∷ [])) ≡ just E.escaped-level
escaped-head = refl
malformed : E.Value
malformed = E.v-neutral (E.n-case (E.n-global "Boundary#packed") [] (tm-var 0) [])
malformed-quote : Previous.failure (Q.run-config true (just C.W.ind) 64 0 malformed) ≡ just E.unbound
malformed-quote = refl
malformed-scope-impossible : Scope.ValueScoped 0 malformed → ⊥
malformed-scope-impossible (Scope.s-neutral (Scope.s-case head Scope.s[] (sc-var ()) branches))
malformed-denotes : Meaning.Denotes 0 malformed (tm-case (tm-global "Boundary#packed") (tm-var 0) [])
malformed-denotes = Meaning.d-neutral (Meaning.d-case Meaning.d-global Meaning.d[])
denotation-alone-does-not-weaken :
  rename wk (tm-case (tm-global "Boundary#packed") (tm-var 0) []) ≢ tm-case (tm-global "Boundary#packed") (tm-var 0) []
denotation-alone-does-not-weaken ()
malformed-branch : E.Value
malformed-branch = E.v-neutral (E.n-case (E.n-global "Boundary#packed") [] tm-atom_type
  (("Boundary#Pack" , 0 , tm-var 0) ∷ []))
malformed-branch-quote : Previous.failure (Q.run-config true (just C.W.ind) 64 0 malformed-branch) ≡ just E.unbound
malformed-branch-quote = refl
malformed-branch-scope-impossible : Scope.ValueScoped 0 malformed-branch → ⊥
malformed-branch-scope-impossible (Scope.s-neutral (Scope.s-case head Scope.s[] motive (sb∷ (sbranch (sc-var ())) rest)))
motive-budget : Previous.failure (Q.normalise-residual-with C.W.ind 16 0
  (tm-case (tm-global "Boundary#packed") Previous.omega []) []) ≡ just E.exhausted
motive-budget = refl
branch-budget : Previous.failure (Q.normalise-residual-with C.W.ind 16 0
  (tm-case (tm-global "Boundary#packed") tm-atom_type (("Boundary#Pack" , 2 , Previous.omega) ∷ [])) []) ≡ just E.exhausted
branch-budget = refl
strict-case-impossible : ∀ {d head env motive branches term}
  → Q.NeutralQuoted d (E.n-case head env motive branches) term → ⊥
strict-case-impossible (Q.q-case () head evaluated motive branches)
data-needs-signature : Previous.failure (Q.normalise-residual 64 0 Observed.data-index-program []) ≡ just E.unsupported
data-needs-signature = refl
wrong-motive-layout : Previous.failure (Q.normalise-residual-with C.W.ind 64 0
  (tm-case (tm-global "Boundary#packed") (tm-data "Boundary#Packed" (tm-atom_type ∷ []) []) []) [])
  ≡ just (E.data-layout Layout.wrong-parameter-arity)
wrong-motive-layout = refl
wrong-value-layout : Previous.failure (Q.run-config true (just C.W.ind) 64 0
  (E.v-data "Boundary#Packed" (E.v-atom-type ∷ []) [])) ≡ just (E.data-layout Layout.wrong-parameter-arity)
wrong-value-layout = refl
exact-arity-retained : Previous.failure (Q.normalise-residual-with C.W.ind 64 0
  (tm-case (tm-ctor "Boundary#Pack" (tm-atom_type ∷ [])) tm-atom_type
    (("Boundary#Pack" , 2 , tm-atom_lit "payload") ∷ [])) []) ≡ just E.arity-mismatch
exact-arity-retained = refl
actual-delta-boundary : present (Normal.check C.W.sig Observed.delta-quoted) ≡ false
actual-delta-boundary = refl
actual-nested-normal : present (Normal.check C.W.sig Observed.typed-scrutinee-quoted) ≡ true
actual-nested-normal = refl
module Administrative = Residual.Administrative C.W.sig
nested-path-invariant : ∀ {endpoint} → _⇝*_ C.W.sig Observed.typed-scrutinee-quoted endpoint
  → Observed.typed-scrutinee-quoted ≡ endpoint
nested-path-invariant = Administrative.path-invariant
  (pick (Normal.check C.W.sig Observed.typed-scrutinee-quoted) actual-nested-normal)
