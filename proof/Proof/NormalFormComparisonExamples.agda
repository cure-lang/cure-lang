{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Equal forms imply native conversion. Distinct/unknown MODEL outcomes
-- do not negate actual Conv (eta, domains and certified delta differ).
------------------------------------------------------------------------
module Proof.NormalFormComparisonExamples where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Typing using (Conversion)
open import Core.Reduction using (δ)
import Core.ClosureEval as E
import Core.NormalFormComparison as Compare
import Core.NativeRecipe as Native
import Proof.NormalFormConversion as Soundness
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableComparison as Observed
open import Proof.CheckedAdmissionExamples using (pick)
module Sound = Soundness.Sound Source.Pin.admission
module C = Sound.C

extract-equal : ∀ {depth env left right} (result : Compare.Verdict depth env left right)
  → Compare.classify result ≡ Compare.equal-forms → Compare.EqualNormal depth env left right
extract-equal (Compare.same evidence) yes = evidence
extract-equal (Compare.distinct evidence) ()
extract-equal (Compare.unknown side reason) ()
module Equal (depth : ℕ) (env : List E.Value) (left right : Term)
  (equal : Compare.classify (Compare.compare 64 depth env left right) ≡ Compare.equal-forms) where
  evidence : Compare.EqualNormal depth env left right
  evidence = extract-equal (Compare.compare 64 depth env left right) equal

module Beta = Equal Observed.beta-depth Observed.beta-environment Observed.beta-left Observed.beta-right refl
module Zeta = Equal Observed.zeta-depth Observed.zeta-environment Observed.zeta-left Observed.zeta-right refl
module Lambda = Equal Observed.lambda-depth Observed.lambda-environment Observed.lambda-left Observed.lambda-right refl
module Pi = Equal Observed.pi-depth Observed.pi-environment Observed.pi-left Observed.pi-right refl
beta-converts : Conversion._≈_ C.W.M.conversion Observed.beta-left Observed.beta-right
beta-converts = Sound.closed-conversion (pick (Native.scope? 0 Observed.beta-left) refl)
  (pick (Native.scope? 0 Observed.beta-right) refl) Beta.evidence
zeta-converts : Conversion._≈_ C.W.M.conversion Observed.zeta-left Observed.zeta-right
zeta-converts = Sound.closed-conversion (pick (Native.scope? 0 Observed.zeta-left) refl)
  (pick (Native.scope? 0 Observed.zeta-right) refl) Zeta.evidence
lambda-converts : Conversion._≈_ C.W.M.conversion Observed.lambda-left Observed.lambda-right
lambda-converts = Sound.closed-conversion (pick (Native.scope? 0 Observed.lambda-left) refl)
  (pick (Native.scope? 0 Observed.lambda-right) refl) Lambda.evidence
pi-converts : Conversion._≈_ C.W.M.conversion Observed.pi-left Observed.pi-right
pi-converts = Sound.closed-conversion (pick (Native.scope? 0 Observed.pi-left) refl)
  (pick (Native.scope? 0 Observed.pi-right) refl) Pi.evidence
actual-beta : Observed.beta-actual ≡ true
actual-beta = refl
actual-zeta : Observed.zeta-actual ≡ true
actual-zeta = refl
actual-lambda : Observed.lambda-actual ≡ true
actual-lambda = refl
actual-pi : Observed.pi-actual ≡ true
actual-pi = refl

lambda-grade-distinct : Compare.classify (Compare.compare 64 Observed.lambda-grade-depth
  Observed.lambda-grade-environment Observed.lambda-grade-left Observed.lambda-grade-right) ≡ Compare.distinct-forms
lambda-grade-distinct = refl
actual-lambda-grade : Observed.lambda-grade-actual ≡ false
actual-lambda-grade = refl
pi-grade-distinct : Compare.classify (Compare.compare 64 Observed.pi-grade-depth
  Observed.pi-grade-environment Observed.pi-grade-left Observed.pi-grade-right) ≡ Compare.distinct-forms
pi-grade-distinct = refl
actual-pi-grade : Observed.pi-grade-actual ≡ false
actual-pi-grade = refl
sorts-distinct : Compare.classify (Compare.compare 64 Observed.universe-depth
  Observed.universe-environment Observed.universe-left Observed.universe-right) ≡ Compare.distinct-forms
sorts-distinct = refl
actual-sorts : Observed.universe-actual ≡ false
actual-sorts = refl
names-distinct : Compare.classify (Compare.compare 64 Observed.name-depth
  Observed.name-environment Observed.name-left Observed.name-right) ≡ Compare.distinct-forms
names-distinct = refl
actual-names : Observed.name-actual ≡ false
actual-names = refl

eta-distinct : Compare.classify (Compare.compare 64 Observed.eta-depth Observed.eta-environment
  Observed.eta-left Observed.eta-right) ≡ Compare.distinct-forms
eta-distinct = refl
actual-eta-accepts : Observed.eta-actual ≡ true
actual-eta-accepts = refl
lambda-domains-distinct : Compare.classify (Compare.compare 64 Observed.domain-depth Observed.domain-environment
  Observed.domain-left Observed.domain-right) ≡ Compare.distinct-forms
lambda-domains-distinct = refl
actual-raw-lambda-domains : Observed.domain-actual ≡ true
actual-raw-lambda-domains = refl
-- The raw API comparison has no shared expected-type guard. This is NOT
-- labelled kernel unsoundness or evidence that mismatched types can check.
delta-distinct : Compare.classify (Compare.compare 64 Observed.delta-depth Observed.delta-environment
  Observed.delta-left Observed.delta-right) ≡ Compare.distinct-forms
delta-distinct = refl
actual-delta-accepts : Observed.delta-actual ≡ true
actual-delta-accepts = refl
distinct-but-native-converts : Conversion._≈_ C.W.M.conversion Observed.delta-left Observed.delta-right
distinct-but-native-converts = C.W.M.reduce-converts
  {t = Observed.delta-left} {u = Observed.delta-right} (δ refl)
data-inconclusive : Compare.classify (Compare.compare 64 Observed.data-depth Observed.data-environment
  Observed.data-left Observed.data-right) ≡ Compare.inconclusive
data-inconclusive = refl
actual-reflexive-data : Observed.data-actual ≡ true
actual-reflexive-data = refl
data-failure-preserved : Compare.compare 64 0 [] Observed.data-left Observed.data-right
  ≡ Compare.unknown Compare.left-side E.unsupported
data-failure-preserved = refl
small-budget : Compare.compare 0 0 [] Observed.beta-left Observed.beta-right
  ≡ Compare.unknown Compare.left-side E.exhausted
small-budget = refl
right-failure-preserved : Compare.compare 64 0 [] tm-atom_type Observed.data-right
  ≡ Compare.unknown Compare.right-side E.unsupported
right-failure-preserved = refl
unbound-is-inconclusive : Compare.compare 64 0 [] (tm-var 0) tm-atom_type
  ≡ Compare.unknown Compare.left-side E.unbound
unbound-is-inconclusive = refl
