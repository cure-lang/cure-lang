{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Data-only serialized requests independently replay inference, both
-- kinds and positive residual conversion at the ORIGINAL expected goal.
------------------------------------------------------------------------
module Proof.ResidualAdmissionExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Core.Syntax
open import Core.Grade using (unrestricted; linear)
open import Core.Universe using (l0; l1; l2)
open import Core.NativeRecipe
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (_⇝*_; ⇝*-refl)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ResidualAdmission as N
import Core.NormalizingAdmission as Strict
import Core.WireResidualChecking as Wire
import Core.WireChecking as StrictWire
import Core.WireConversion as Tags
import Core.ResidualComparison as Compare
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quotation
import Proof.Substitution as Substitution
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableBundle as Bundle
import Fixtures.ExecutableResidualComparison as Produced
module R = N.Replay Source.Pin.admission
module Chars = Wire.Replay Source.Pin.admission
module Old = Strict.Replay Source.Pin.admission
module OldChars = StrictWire.Replay Source.Pin.admission
module Model = Quotation.Simulation R.C.W.sig

choose : ∀ {A} (result : N.Result A) → N.present result ≡ true → A
choose (N.accepted value) accepted = value
choose (N.rejected reason) ()
eval-present : ∀ {A} → E.Result A → Bool
eval-present (E.done value) = true
eval-present (E.stop reason) = false
eval-choose : ∀ {A} (result : E.Result A) → eval-present result ≡ true → A
eval-choose (E.done value) accepted = value
eval-choose (E.stop reason) ()
decoded-witness : ∀ {A} (input : Maybe A) (accepted : present input ≡ true)
  → input ≡ just (pick input accepted)
decoded-witness nothing ()
decoded-witness (just value) accepted = refl
query-of : (characters : List Char) → present (Wire.decode Bundle.table characters) ≡ true → N.Request
query-of characters parsed = pick (Wire.decode Bundle.table characters) parsed
normalized-basis : ∀ {left right} → N.Basis left right → Bool
normalized-basis (N.exact same) = false
normalized-basis (N.normalized equal) = true

module Example (characters : List Char) (parsed : present (Wire.decode Bundle.table characters) ≡ true)
  (accepted : N.present (R.verify 64 (query-of characters parsed)) ≡ true)
  (quoted : eval-present (Q.normalise-residual-with R.C.W.ind 64 0
    (N.Request.subject (query-of characters parsed)) []) ≡ true) where
  query : N.Request
  query = query-of characters parsed
  decoded : Wire.decode Bundle.table characters ≡ just query
  decoded = decoded-witness (Wire.decode Bundle.table characters) parsed
  wire-positive : N.present (Chars.verify 64 characters) ≡ true
  wire-positive = trans (Chars.verify-decoded 64 characters query decoded) accepted
  wire-checked : Chars.Checked 64 characters
  wire-checked = choose (Chars.verify 64 characters) wire-positive
  checked : R.Checked query
  checked = Chars.pin wire-checked query decoded
  safe : R.C.Sound.SafeState (N.Request.subject query) (N.Request.goal query)
  safe = R.Checked.trace-safe checked ⇝*-refl
  tree : R.C.Sound.EvalTree (N.Request.subject query) (N.Request.goal query)
  tree = R.Checked.tree checked
  budgets-agree : ∀ budget → R.Checked.run checked budget ≡ R.C.Sound.truncate budget tree
  budgets-agree = R.Checked.budgets-agree checked
  readback : Σ Term (Q.ResidualNormalizes 0 [] (N.Request.subject query))
  readback = eval-choose (Q.normalise-residual-with R.C.W.ind 64 0 (N.Request.subject query) []) quoted
  readback-path : _⇝*_ R.C.W.sig (N.Request.subject query) (proj₁ readback)
  readback-path = Model.O.⇝*-trans
    (Model.Eval.equal-path (sym (Substitution.substS-idSub (N.Request.subject query))))
    (Model.residual-normalization Scope.s[] (R.R.scoped (R.Checked.subject-supported checked)) Meaning.d[] (proj₂ readback))
  readback-safe : R.C.Sound.SafeState (proj₁ readback) (N.Request.goal query)
  readback-safe = R.Checked.trace-safe checked readback-path

module Residual = Example Produced.residual-characters refl refl refl
module Reverse = Example Produced.reverse-characters refl refl refl
module DataCase = Example Produced.data-characters refl refl refl
module Nested = Example Produced.nested-characters refl refl refl

residual-inferred : R.Checked.inferred Residual.checked ≡ Produced.residual-inferred
residual-inferred = refl
reverse-inferred : R.Checked.inferred Reverse.checked ≡ Produced.reverse-inferred
reverse-inferred = refl
data-inferred : R.Checked.inferred DataCase.checked ≡ Produced.data-inferred
data-inferred = refl
nested-inferred : R.Checked.inferred Nested.checked ≡ Produced.nested-inferred
nested-inferred = refl
residual-used-normalization : normalized-basis (R.Checked.basis Residual.checked) ≡ true
residual-used-normalization = refl
reverse-used-normalization : normalized-basis (R.Checked.basis Reverse.checked) ≡ true
reverse-used-normalization = refl
data-used-normalization : normalized-basis (R.Checked.basis DataCase.checked) ≡ true
data-used-normalization = refl
nested-used-normalization : normalized-basis (R.Checked.basis Nested.checked) ≡ true
nested-used-normalization = refl

-- Zero comparison fuel cannot skip any source/inferred/goal guard.
exact-query : N.Request
exact-query = record Residual.query
  { goal = Produced.residual-inferred ; goal-kind-recipe = N.Request.inferred-kind-recipe Residual.query }
exact-zero : N.present (R.verify 0 exact-query) ≡ true
exact-zero = refl
strict-exact-still-works : N.present (Old.verify 0 exact-query) ≡ true
strict-exact-still-works = refl
strict-nonexact-still-fails : Old.verify 64 Residual.query
  ≡ N.rejected (N.inconclusive Compare.left-side E.neutral-scrutinee)
strict-nonexact-still-fails = refl
strict-wire-still-fails : OldChars.verify 64 Produced.residual-characters
  ≡ N.rejected (N.inconclusive Compare.left-side E.neutral-scrutinee)
strict-wire-still-fails = refl
nonexact-needs-budget : R.verify 0 Residual.query ≡ N.rejected (N.inconclusive Compare.left-side E.exhausted)
nonexact-needs-budget = refl
inferred-kind-before-exact : R.verify 0 (record exact-query { inferred-kind-recipe = r-lam r-leaf r-leaf })
  ≡ N.rejected N.inferred-kind-failed
inferred-kind-before-exact = refl
goal-kind-before-exact : R.verify 0 (record exact-query { goal-kind-recipe = r-lam r-leaf r-leaf })
  ≡ N.rejected N.goal-kind-failed
goal-kind-before-exact = refl
not-a-type : R.verify 64 (record Residual.query { goal = tm-atom_lit "payload" ; goal-kind-recipe = r-leaf })
  ≡ N.rejected N.goal-kind-failed
not-a-type = refl
universe-ceiling : N.present (R.verify 64 (record Residual.query { goal = tm-type l2 ; goal-kind-recipe = r-leaf })) ≡ false
universe-ceiling = refl
escaped-subject : R.verify 64 (record Residual.query { subject = tm-var 0 }) ≡ N.rejected N.unsupported-subject
escaped-subject = refl
forged-inference : R.verify 64 (record Residual.query { subject-recipe = r-leaf }) ≡ N.rejected N.inference-failed
forged-inference = refl
wrong-grade : N.present (R.verify 64 (record Residual.query
  { goal = tm-pi linear tm-atom_type tm-atom_type ; goal-kind-recipe = r-pi r-leaf r-leaf })) ≡ false
wrong-grade = refl
cumulative-query : N.Request
cumulative-query = N.request tm-atom_type r-leaf r-leaf (tm-type l1) r-leaf
cumulativity-is-not-equality : N.present (R.verify 64 cumulative-query) ≡ false
cumulativity-is-not-equality = refl
explicit-cumulativity : N.present (R.verify 0 (record cumulative-query { subject-recipe = r-cumul l1 r-leaf })) ≡ true
explicit-cumulativity = refl
malformed : Chars.verify 64 ('(' ∷ []) ≡ N.rejected N.malformed-wire
malformed = refl
trailing : N.present (Chars.verify 64 (Produced.residual-characters ++ (';' ∷ []))) ≡ false
trailing = refl
wrong-tag : Wire.from-node Bundle.table (Tags.tagged 19 []) ≡ nothing
wrong-tag = refl
missing-name : Wire.to-node [] Residual.query ≡ nothing
missing-name = refl
