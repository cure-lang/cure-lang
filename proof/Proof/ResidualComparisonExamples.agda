{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Fixed actual readbacks/Conv results are observations, not a universal
-- implementation theorem. Distinct eta/delta forms are not refutations.
------------------------------------------------------------------------
module Proof.ResidualComparisonExamples where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Typing using (Conversion)
open import Core.NativeRecipe using (scope?)
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (_⇝*_; δ; ⇝*-step; ⇝*-refl)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.ResidualComparison as Compare
import Core.NormalFormComparison as Strict
import Core.ResidualNormal as Normal
import Proof.ResidualNormal as Residual
import Proof.ResidualConversion as Model
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureEvaluationExamples as Previous
import Proof.ClosureQuotationExamples as OldQuote
import Proof.WireSnapshotExamples as Source
import Proof.ResidualQuotationSafetyExamples as Caller
import Fixtures.ExecutableResidualComparison as Observed
import Fixtures.ExecutableResidualQuotation as Prior
module C = Previous.C
module Sound = Model.Sound Source.Pin.admission

equal : ∀ {d env l r} (result : Compare.Verdict d env l r)
  → Compare.classify result ≡ Compare.equal-forms → Compare.EqualResidual d env l r
equal (Compare.same evidence) accepted = evidence
equal (Compare.distinct evidence) ()
equal (Compare.unknown side reason) ()

module Observation (d : ℕ) (env : List E.Value) (left right lq rq : Term) (classification : Compare.Classification)
  (left-agrees : OldQuote.term-result (Q.normalise-residual-with C.W.ind 64 d left env) ≡ just lq)
  (right-agrees : OldQuote.term-result (Q.normalise-residual-with C.W.ind 64 d right env) ≡ just rq)
  (classified : Compare.classify (Compare.compare-with C.W.ind 64 d env left right) ≡ classification)
  (left-scoped : present (scope? (length env) left) ≡ true)
  (right-scoped : present (scope? (length env) right) ≡ true) where
  left-execution : Q.ResidualNormalizes d env left lq
  left-execution = OldQuote.extract (Q.normalise-residual-with C.W.ind 64 d left env) lq left-agrees
  right-execution : Q.ResidualNormalizes d env right rq
  right-execution = OldQuote.extract (Q.normalise-residual-with C.W.ind 64 d right env) rq right-agrees
  left-scope : Scoped (length env) left
  left-scope = pick (scope? (length env) left) left-scoped
  right-scope : Scoped (length env) right
  right-scope = pick (scope? (length env) right) right-scoped

module Positive (d : ℕ) (env : List E.Value) (left right : Term)
  (classified : Compare.classify (Compare.compare-with C.W.ind 64 d env left right) ≡ Compare.equal-forms)
  (left-scoped : present (scope? (length env) left) ≡ true)
  (right-scoped : present (scope? (length env) right) ≡ true)
  (actual : Bool) (actual-positive : actual ≡ true) where
  evidence : Compare.EqualResidual d env left right
  evidence = equal (Compare.compare-with C.W.ind 64 d env left right) classified
  normal : Normal.Normal Residual.no-delta (Compare.EqualResidual.common evidence)
  normal = Model.normal evidence
  converts : ∀ {terms} → Scope.EnvironmentScoped d env → Meaning.Environments d env terms
    → Conversion._≈_ C.W.M.conversion
      (substS (Meaning.environment-sub terms) left) (substS (Meaning.environment-sub terms) right)
  converts scoped denoted = Sound.conversion scoped (pick (scope? (length env) left) left-scoped)
    (pick (scope? (length env) right) right-scoped) denoted evidence

-- Literal observation instances.

module ReplayOpaque = Observation Observed.opaque-depth Observed.opaque-environment
  Observed.opaque-left Observed.opaque-right Observed.opaque-left-quoted Observed.opaque-right-quoted
  Observed.opaque-classification refl refl refl refl refl
module EqualOpaque = Positive Observed.opaque-depth Observed.opaque-environment
  Observed.opaque-left Observed.opaque-right refl refl refl Observed.opaque-actual refl
module ReplayBranch = Observation Observed.branch-depth Observed.branch-environment
  Observed.branch-left Observed.branch-right Observed.branch-left-quoted Observed.branch-right-quoted
  Observed.branch-classification refl refl refl refl refl
module EqualBranch = Positive Observed.branch-depth Observed.branch-environment
  Observed.branch-left Observed.branch-right refl refl refl Observed.branch-actual refl
module ReplayMotive = Observation Observed.motive-depth Observed.motive-environment
  Observed.motive-left Observed.motive-right Observed.motive-left-quoted Observed.motive-right-quoted
  Observed.motive-classification refl refl refl refl refl
module EqualMotive = Positive Observed.motive-depth Observed.motive-environment
  Observed.motive-left Observed.motive-right refl refl refl Observed.motive-actual refl
module ReplayScrutinee = Observation Observed.scrutinee-depth Observed.scrutinee-environment
  Observed.scrutinee-left Observed.scrutinee-right Observed.scrutinee-left-quoted Observed.scrutinee-right-quoted
  Observed.scrutinee-classification refl refl refl refl refl
module EqualScrutinee = Positive Observed.scrutinee-depth Observed.scrutinee-environment
  Observed.scrutinee-left Observed.scrutinee-right refl refl refl Observed.scrutinee-actual refl
module ReplayOpen = Observation Observed.open-depth Observed.open-environment
  Observed.open-left Observed.open-right Observed.open-left-quoted Observed.open-right-quoted
  Observed.open-classification refl refl refl refl refl
module EqualOpen = Positive Observed.open-depth Observed.open-environment
  Observed.open-left Observed.open-right refl refl refl Observed.open-actual refl
module ReplaySpine = Observation Observed.spine-depth Observed.spine-environment
  Observed.spine-left Observed.spine-right Observed.spine-left-quoted Observed.spine-right-quoted
  Observed.spine-classification refl refl refl refl refl
module EqualSpine = Positive Observed.spine-depth Observed.spine-environment
  Observed.spine-left Observed.spine-right refl refl refl Observed.spine-actual refl
module ReplayZero = Observation Observed.zero-depth Observed.zero-environment
  Observed.zero-left Observed.zero-right Observed.zero-left-quoted Observed.zero-right-quoted
  Observed.zero-classification refl refl refl refl refl
module EqualZero = Positive Observed.zero-depth Observed.zero-environment
  Observed.zero-left Observed.zero-right refl refl refl Observed.zero-actual refl
module ReplayMulti = Observation Observed.multi-depth Observed.multi-environment
  Observed.multi-left Observed.multi-right Observed.multi-left-quoted Observed.multi-right-quoted
  Observed.multi-classification refl refl refl refl refl
module EqualMulti = Positive Observed.multi-depth Observed.multi-environment
  Observed.multi-left Observed.multi-right refl refl refl Observed.multi-actual refl
module ReplayCapture = Observation Observed.capture-depth Observed.capture-environment
  Observed.capture-left Observed.capture-right Observed.capture-left-quoted Observed.capture-right-quoted
  Observed.capture-classification refl refl refl refl refl
module EqualCapture = Positive Observed.capture-depth Observed.capture-environment
  Observed.capture-left Observed.capture-right refl refl refl Observed.capture-actual refl
module ReplayData = Observation Observed.data-depth Observed.data-environment
  Observed.data-left Observed.data-right Observed.data-left-quoted Observed.data-right-quoted
  Observed.data-classification refl refl refl refl refl
module EqualData = Positive Observed.data-depth Observed.data-environment
  Observed.data-left Observed.data-right refl refl refl Observed.data-actual refl
module ReplaySharedCase = Observation Observed.shared-case-depth Observed.shared-case-environment
  Observed.shared-case-left Observed.shared-case-right Observed.shared-case-left-quoted Observed.shared-case-right-quoted
  Observed.shared-case-classification refl refl refl refl refl
module EqualSharedCase = Positive Observed.shared-case-depth Observed.shared-case-environment
  Observed.shared-case-left Observed.shared-case-right refl refl refl Observed.shared-case-actual refl
module ReplayDelta = Observation Observed.delta-depth Observed.delta-environment
  Observed.delta-left Observed.delta-right Observed.delta-left-quoted Observed.delta-right-quoted
  Observed.delta-classification refl refl refl refl refl
module EqualDelta = Positive Observed.delta-depth Observed.delta-environment
  Observed.delta-left Observed.delta-right refl refl refl Observed.delta-actual refl
module ReplayNestedScrutinee = Observation Observed.nested-scrutinee-depth Observed.nested-scrutinee-environment
  Observed.nested-scrutinee-left Observed.nested-scrutinee-right Observed.nested-scrutinee-left-quoted Observed.nested-scrutinee-right-quoted
  Observed.nested-scrutinee-classification refl refl refl refl refl
module EqualNestedScrutinee = Positive Observed.nested-scrutinee-depth Observed.nested-scrutinee-environment
  Observed.nested-scrutinee-left Observed.nested-scrutinee-right refl refl refl Observed.nested-scrutinee-actual refl
module ReplayNestedBranch = Observation Observed.nested-branch-depth Observed.nested-branch-environment
  Observed.nested-branch-left Observed.nested-branch-right Observed.nested-branch-left-quoted Observed.nested-branch-right-quoted
  Observed.nested-branch-classification refl refl refl refl refl
module EqualNestedBranch = Positive Observed.nested-branch-depth Observed.nested-branch-environment
  Observed.nested-branch-left Observed.nested-branch-right refl refl refl Observed.nested-branch-actual refl
module ReplayLamBody = Observation Observed.lam-body-depth Observed.lam-body-environment
  Observed.lam-body-left Observed.lam-body-right Observed.lam-body-left-quoted Observed.lam-body-right-quoted
  Observed.lam-body-classification refl refl refl refl refl
module EqualLamBody = Positive Observed.lam-body-depth Observed.lam-body-environment
  Observed.lam-body-left Observed.lam-body-right refl refl refl Observed.lam-body-actual refl
module ReplayLamDomain = Observation Observed.lam-domain-depth Observed.lam-domain-environment
  Observed.lam-domain-left Observed.lam-domain-right Observed.lam-domain-left-quoted Observed.lam-domain-right-quoted
  Observed.lam-domain-classification refl refl refl refl refl
module EqualLamDomain = Positive Observed.lam-domain-depth Observed.lam-domain-environment
  Observed.lam-domain-left Observed.lam-domain-right refl refl refl Observed.lam-domain-actual refl
module ReplayPiBody = Observation Observed.pi-body-depth Observed.pi-body-environment
  Observed.pi-body-left Observed.pi-body-right Observed.pi-body-left-quoted Observed.pi-body-right-quoted
  Observed.pi-body-classification refl refl refl refl refl
module EqualPiBody = Positive Observed.pi-body-depth Observed.pi-body-environment
  Observed.pi-body-left Observed.pi-body-right refl refl refl Observed.pi-body-actual refl
module ReplayCtorField = Observation Observed.ctor-field-depth Observed.ctor-field-environment
  Observed.ctor-field-left Observed.ctor-field-right Observed.ctor-field-left-quoted Observed.ctor-field-right-quoted
  Observed.ctor-field-classification refl refl refl refl refl
module EqualCtorField = Positive Observed.ctor-field-depth Observed.ctor-field-environment
  Observed.ctor-field-left Observed.ctor-field-right refl refl refl Observed.ctor-field-actual refl
module ReplayDataIndex = Observation Observed.data-index-depth Observed.data-index-environment
  Observed.data-index-left Observed.data-index-right Observed.data-index-left-quoted Observed.data-index-right-quoted
  Observed.data-index-classification refl refl refl refl refl
module EqualDataIndex = Positive Observed.data-index-depth Observed.data-index-environment
  Observed.data-index-left Observed.data-index-right refl refl refl Observed.data-index-actual refl
module ReplayNeutralFunction = Observation Observed.neutral-function-depth Observed.neutral-function-environment
  Observed.neutral-function-left Observed.neutral-function-right Observed.neutral-function-left-quoted Observed.neutral-function-right-quoted
  Observed.neutral-function-classification refl refl refl refl refl
module EqualNeutralFunction = Positive Observed.neutral-function-depth Observed.neutral-function-environment
  Observed.neutral-function-left Observed.neutral-function-right refl refl refl Observed.neutral-function-actual refl
module ReplayNeutralArgument = Observation Observed.neutral-argument-depth Observed.neutral-argument-environment
  Observed.neutral-argument-left Observed.neutral-argument-right Observed.neutral-argument-left-quoted Observed.neutral-argument-right-quoted
  Observed.neutral-argument-classification refl refl refl refl refl
module EqualNeutralArgument = Positive Observed.neutral-argument-depth Observed.neutral-argument-environment
  Observed.neutral-argument-left Observed.neutral-argument-right refl refl refl Observed.neutral-argument-actual refl
module ReplayBetaArgument = Observation Observed.beta-argument-depth Observed.beta-argument-environment
  Observed.beta-argument-left Observed.beta-argument-right Observed.beta-argument-left-quoted Observed.beta-argument-right-quoted
  Observed.beta-argument-classification refl refl refl refl refl
module EqualBetaArgument = Positive Observed.beta-argument-depth Observed.beta-argument-environment
  Observed.beta-argument-left Observed.beta-argument-right refl refl refl Observed.beta-argument-actual refl
module ReplayLetCapture = Observation Observed.let-capture-depth Observed.let-capture-environment
  Observed.let-capture-left Observed.let-capture-right Observed.let-capture-left-quoted Observed.let-capture-right-quoted
  Observed.let-capture-classification refl refl refl refl refl
module EqualLetCapture = Positive Observed.let-capture-depth Observed.let-capture-environment
  Observed.let-capture-left Observed.let-capture-right refl refl refl Observed.let-capture-actual refl
module ReplayEnvironment = Observation Observed.environment-depth Observed.environment-environment
  Observed.environment-left Observed.environment-right Observed.environment-left-quoted Observed.environment-right-quoted
  Observed.environment-classification refl refl refl refl refl
module EqualEnvironment = Positive Observed.environment-depth Observed.environment-environment
  Observed.environment-left Observed.environment-right refl refl refl Observed.environment-actual refl
module ReplayFreshCapture = Observation Observed.fresh-capture-depth Observed.fresh-capture-environment
  Observed.fresh-capture-left Observed.fresh-capture-right Observed.fresh-capture-left-quoted Observed.fresh-capture-right-quoted
  Observed.fresh-capture-classification refl refl refl refl refl
module EqualFreshCapture = Positive Observed.fresh-capture-depth Observed.fresh-capture-environment
  Observed.fresh-capture-left Observed.fresh-capture-right refl refl refl Observed.fresh-capture-actual refl
module ReplayExactCase = Observation Observed.exact-case-depth Observed.exact-case-environment
  Observed.exact-case-left Observed.exact-case-right Observed.exact-case-left-quoted Observed.exact-case-right-quoted
  Observed.exact-case-classification refl refl refl refl refl
module EqualExactCase = Positive Observed.exact-case-depth Observed.exact-case-environment
  Observed.exact-case-left Observed.exact-case-right refl refl refl Observed.exact-case-actual refl
module ReplayNestedMotive = Observation Observed.nested-motive-depth Observed.nested-motive-environment
  Observed.nested-motive-left Observed.nested-motive-right Observed.nested-motive-left-quoted Observed.nested-motive-right-quoted
  Observed.nested-motive-classification refl refl refl refl refl
module EqualNestedMotive = Positive Observed.nested-motive-depth Observed.nested-motive-environment
  Observed.nested-motive-left Observed.nested-motive-right refl refl refl Observed.nested-motive-actual refl
module ReplayBranchBinder = Observation Observed.branch-binder-depth Observed.branch-binder-environment
  Observed.branch-binder-left Observed.branch-binder-right Observed.branch-binder-left-quoted Observed.branch-binder-right-quoted
  Observed.branch-binder-classification refl refl refl refl refl
module EqualBranchBinder = Positive Observed.branch-binder-depth Observed.branch-binder-environment
  Observed.branch-binder-left Observed.branch-binder-right refl refl refl Observed.branch-binder-actual refl
module ReplayTriple = Observation Observed.triple-depth Observed.triple-environment
  Observed.triple-left Observed.triple-right Observed.triple-left-quoted Observed.triple-right-quoted
  Observed.triple-classification refl refl refl refl refl
module EqualTriple = Positive Observed.triple-depth Observed.triple-environment
  Observed.triple-left Observed.triple-right refl refl refl Observed.triple-actual refl
module ReplayTypedScrutinee = Observation Observed.typed-scrutinee-depth Observed.typed-scrutinee-environment
  Observed.typed-scrutinee-left Observed.typed-scrutinee-right Observed.typed-scrutinee-left-quoted Observed.typed-scrutinee-right-quoted
  Observed.typed-scrutinee-classification refl refl refl refl refl
module EqualTypedScrutinee = Positive Observed.typed-scrutinee-depth Observed.typed-scrutinee-environment
  Observed.typed-scrutinee-left Observed.typed-scrutinee-right refl refl refl Observed.typed-scrutinee-actual refl
module ReplayTypedBranch = Observation Observed.typed-branch-depth Observed.typed-branch-environment
  Observed.typed-branch-left Observed.typed-branch-right Observed.typed-branch-left-quoted Observed.typed-branch-right-quoted
  Observed.typed-branch-classification refl refl refl refl refl
module EqualTypedBranch = Positive Observed.typed-branch-depth Observed.typed-branch-environment
  Observed.typed-branch-left Observed.typed-branch-right refl refl refl Observed.typed-branch-actual refl
module ReplayCheckingResidual = Observation Observed.checking-residual-depth Observed.checking-residual-environment
  Observed.checking-residual-left Observed.checking-residual-right Observed.checking-residual-left-quoted Observed.checking-residual-right-quoted
  Observed.checking-residual-classification refl refl refl refl refl
module EqualCheckingResidual = Positive Observed.checking-residual-depth Observed.checking-residual-environment
  Observed.checking-residual-left Observed.checking-residual-right refl refl refl Observed.checking-residual-actual refl
module ReplayCheckingReverse = Observation Observed.checking-reverse-depth Observed.checking-reverse-environment
  Observed.checking-reverse-left Observed.checking-reverse-right Observed.checking-reverse-left-quoted Observed.checking-reverse-right-quoted
  Observed.checking-reverse-classification refl refl refl refl refl
module EqualCheckingReverse = Positive Observed.checking-reverse-depth Observed.checking-reverse-environment
  Observed.checking-reverse-left Observed.checking-reverse-right refl refl refl Observed.checking-reverse-actual refl
module ReplayCheckingData = Observation Observed.checking-data-depth Observed.checking-data-environment
  Observed.checking-data-left Observed.checking-data-right Observed.checking-data-left-quoted Observed.checking-data-right-quoted
  Observed.checking-data-classification refl refl refl refl refl
module EqualCheckingData = Positive Observed.checking-data-depth Observed.checking-data-environment
  Observed.checking-data-left Observed.checking-data-right refl refl refl Observed.checking-data-actual refl
module ReplayCheckingNested = Observation Observed.checking-nested-depth Observed.checking-nested-environment
  Observed.checking-nested-left Observed.checking-nested-right Observed.checking-nested-left-quoted Observed.checking-nested-right-quoted
  Observed.checking-nested-classification refl refl refl refl refl
module EqualCheckingNested = Positive Observed.checking-nested-depth Observed.checking-nested-environment
  Observed.checking-nested-left Observed.checking-nested-right refl refl refl Observed.checking-nested-actual refl
module ReplayDeltaBoundary = Observation Observed.delta-boundary-depth Observed.delta-boundary-environment
  Observed.delta-boundary-left Observed.delta-boundary-right Observed.delta-boundary-left-quoted Observed.delta-boundary-right-quoted
  Observed.delta-boundary-classification refl refl refl refl refl
module ReplayEtaBoundary = Observation Observed.eta-boundary-depth Observed.eta-boundary-environment
  Observed.eta-boundary-left Observed.eta-boundary-right Observed.eta-boundary-left-quoted Observed.eta-boundary-right-quoted
  Observed.eta-boundary-classification refl refl refl refl refl
module ReplayGradeBoundary = Observation Observed.grade-boundary-depth Observed.grade-boundary-environment
  Observed.grade-boundary-left Observed.grade-boundary-right Observed.grade-boundary-left-quoted Observed.grade-boundary-right-quoted
  Observed.grade-boundary-classification refl refl refl refl refl
module ReplayUniverseBoundary = Observation Observed.universe-boundary-depth Observed.universe-boundary-environment
  Observed.universe-boundary-left Observed.universe-boundary-right Observed.universe-boundary-left-quoted Observed.universe-boundary-right-quoted
  Observed.universe-boundary-classification refl refl refl refl refl
module ReplayNameBoundary = Observation Observed.name-boundary-depth Observed.name-boundary-environment
  Observed.name-boundary-left Observed.name-boundary-right Observed.name-boundary-left-quoted Observed.name-boundary-right-quoted
  Observed.name-boundary-classification refl refl refl refl refl
module ReplayArityBoundary = Observation Observed.arity-boundary-depth Observed.arity-boundary-environment
  Observed.arity-boundary-left Observed.arity-boundary-right Observed.arity-boundary-left-quoted Observed.arity-boundary-right-quoted
  Observed.arity-boundary-classification refl refl refl refl refl

delta-actual-positive : Observed.delta-boundary-actual ≡ true
delta-actual-positive = refl
eta-actual-positive : Observed.eta-boundary-actual ≡ true
eta-actual-positive = refl
delta-forms-differ : Observed.delta-boundary-classification ≡ Compare.distinct-forms
delta-forms-differ = refl
eta-forms-differ : Observed.eta-boundary-classification ≡ Compare.distinct-forms
eta-forms-differ = refl
-- A native delta conversion EXISTS despite the comparator's distinct result.
delta-native-conversion : Conversion._≈_ C.W.M.conversion Observed.delta-boundary-left Observed.delta-boundary-right
delta-native-conversion = _ , C.W.M.E.expand-star (⇝*-step (δ refl) ⇝*-refl) ,
  C.W.M.E.expand-star {t = Observed.delta-boundary-right} ⇝*-refl

strict-still-fails : Strict.compare-with C.W.ind 64 0 [] Observed.branch-left Observed.branch-right
  ≡ Strict.unknown Strict.left-side E.neutral-scrutinee
strict-still-fails = refl
left-budget : Compare.compare-with C.W.ind 0 0 [] tm-atom_type tm-atom_type
  ≡ Compare.unknown Compare.left-side E.exhausted
left-budget = refl
right-unbound : Compare.compare-with C.W.ind 64 0 [] tm-atom_type (tm-var 0)
  ≡ Compare.unknown Compare.right-side E.unbound
right-unbound = refl
left-unbound : Compare.compare-with C.W.ind 64 0 [] (tm-var 0) tm-atom_type
  ≡ Compare.unknown Compare.left-side E.unbound
left-unbound = refl
right-omega : Compare.compare-with C.W.ind 16 0 [] tm-atom_type Previous.omega
  ≡ Compare.unknown Compare.right-side E.exhausted
right-omega = refl
no-data-fallback : Compare.compare 64 0 [] Observed.checking-data-left Observed.checking-data-right
  ≡ Compare.unknown Compare.left-side E.unsupported
no-data-fallback = refl
-- The comparator itself intentionally has no exact-reflexivity shortcut.
same-omega-is-inconclusive : Compare.compare-with C.W.ind 16 0 [] Previous.omega Previous.omega
  ≡ Compare.unknown Compare.left-side E.exhausted
same-omega-is-inconclusive = refl

branch-conversion : Conversion._≈_ C.W.M.conversion Observed.branch-left Observed.branch-right
branch-conversion = EqualBranch.converts Scope.s[] Meaning.d[]
open-conversion : Conversion._≈_ C.W.M.conversion Observed.open-left Observed.open-right
open-conversion = EqualOpen.converts
  (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[])
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])
fresh-capture-conversion : Conversion._≈_ C.W.M.conversion
  (substS (Meaning.environment-sub (Prior.opaque-program ∷ [])) Observed.fresh-capture-left)
  (substS (Meaning.environment-sub (Prior.opaque-program ∷ [])) Observed.fresh-capture-right)
fresh-capture-conversion = EqualFreshCapture.converts Caller.environment-scope Caller.environment-denotes
delta-common-not-actual-normal : present (Normal.check C.W.sig (Compare.EqualResidual.common EqualDelta.evidence)) ≡ false
delta-common-not-actual-normal = refl
strict-evidence : Strict.EqualNormal 0 [] tm-atom_type tm-atom_type
strict-evidence = record
  { common = tm-atom_type
  ; left-execution = Q.normalized E.v-atom-type E.e-atom-type Q.q-atom-type
  ; right-execution = Q.normalized E.v-atom-type E.e-atom-type Q.q-atom-type }
strict-evidence-embeds : Compare.EqualResidual 0 [] tm-atom_type tm-atom_type
strict-evidence-embeds = Model.from-strict strict-evidence
