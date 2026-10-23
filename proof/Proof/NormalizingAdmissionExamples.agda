{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Native expected-goal admission without an input conversion recipe.
-- The literal request derives conversion through bounded normalization.
------------------------------------------------------------------------
module Proof.NormalizingAdmissionExamples where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Core.Syntax
open import Core.Universe using (l0; l1; l2)
open import Core.Grade using (linear; unrestricted)
open import Core.NativeRecipe
open import Core.Reduction using (⇝*-refl)
import Core.NormalizingAdmission as N
import Core.WireChecking as Wire
import Core.WireConversion as Tags
import Core.NormalFormComparison as Compare
import Core.ClosureEval as E
import Proof.WireSnapshotExamples as Source
import Proof.NativeCertificateExamples as Existing
import Proof.NativeRecipeExamples as Recipes
import Fixtures.ExecutableBundle as Bundle
import Fixtures.ExecutableChecking as Produced
module R = N.Replay Source.Pin.admission
module Chars = Wire.Replay Source.Pin.admission

pick : ∀ {A} (result : N.Result A) → N.present result ≡ true → A
pick (N.accepted value) successful = value
pick (N.rejected reason) ()

beta-type : Term
beta-type = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-atom_type
beta-kind : Recipe
beta-kind = r-app (r-lam r-leaf r-leaf) r-leaf
query : N.Request
query = N.request (tm-atom_lit "payload") r-leaf r-leaf beta-type beta-kind
encoded : Wire.encode Bundle.table query ≡ just Produced.characters
encoded = refl
decoded : Wire.decode Bundle.table Produced.characters ≡ just query
decoded = Wire.roundtrip Bundle.table query Produced.characters encoded
accepted : N.present (Chars.verify 64 Produced.characters) ≡ true
accepted = trans (Chars.verify-decoded 64 Produced.characters query decoded) refl
wire-checked : Chars.Checked 64 Produced.characters
wire-checked = pick (Chars.verify 64 Produced.characters) accepted
checked : R.Checked query
checked = Chars.pin wire-checked query decoded
original-goal-safe : R.C.Sound.SafeState (tm-atom_lit "payload") beta-type
original-goal-safe = R.Checked.trace-safe checked ⇝*-refl
source-actually-inferred : R.Checked.inferred (pick (R.verify 64 query) refl) ≡ tm-atom_type
source-actually-inferred = refl
-- The result's proof retains the ORIGINAL beta-redex goal, not its normal form.
tree : R.C.Sound.EvalTree (tm-atom_lit "payload") beta-type
tree = R.Checked.tree checked
budgets-agree : ∀ budget → R.Checked.run checked budget ≡ R.C.Sound.truncate budget tree
budgets-agree = R.Checked.budgets-agree checked

lambda-query : N.Request
lambda-query = N.request (tm-lam unrestricted tm-atom_type (tm-var 0))
  (r-lam r-leaf r-leaf) (r-pi r-leaf r-leaf)
  (tm-pi unrestricted tm-atom_type beta-type) (r-pi r-leaf beta-kind)
lambda-checked : R.Checked lambda-query
lambda-checked = pick (R.verify 64 lambda-query) refl
lambda-safe : R.C.Sound.SafeState (N.Request.subject lambda-query) (N.Request.goal lambda-query)
lambda-safe = R.Checked.trace-safe lambda-checked ⇝*-refl
dependent-goal : Term
dependent-goal = tm-pi unrestricted (tm-type l0)
  (tm-pi unrestricted (tm-var 0) (tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) (tm-var 1)))
dependent-query : N.Request
dependent-query = N.request Recipes.dependent-lambda (r-lam r-leaf (r-lam r-leaf r-leaf))
  (r-pi r-leaf (r-pi r-leaf r-leaf)) dependent-goal (r-pi r-leaf (r-pi r-leaf beta-kind))
dependent-checked : R.Checked dependent-query
dependent-checked = pick (R.verify 64 dependent-query) refl
dependent-safe : R.C.Sound.SafeState Recipes.dependent-lambda dependent-goal
dependent-safe = R.Checked.trace-safe dependent-checked ⇝*-refl

data-query : N.Request
data-query = N.request Existing.value (r-ctor [] [] (r-leaf ∷ r-leaf ∷ []))
  (r-data [] (r-leaf ∷ [])) Existing.goal (r-data [] (r-leaf ∷ []))
data-exact-with-zero-budget : N.present (R.verify 0 data-query) ≡ true
data-exact-with-zero-budget = refl
data-checked : R.Checked data-query
data-checked = pick (R.verify 0 data-query) data-exact-with-zero-budget
data-safe : R.C.Sound.SafeState Existing.value Existing.goal
data-safe = R.Checked.trace-safe data-checked ⇝*-refl
data-beta-query : N.Request
data-beta-query = record data-query
  { goal = tm-app (tm-lam unrestricted (tm-type l1) (tm-var 0)) Existing.goal
  ; goal-kind-recipe = r-app (r-lam r-leaf r-leaf) (r-data [] (r-leaf ∷ [])) }
data-comparison-now-checked : N.present (R.verify 64 data-beta-query) ≡ true
data-comparison-now-checked = refl
data-beta-checked : R.Checked data-beta-query
data-beta-checked = pick (R.verify 64 data-beta-query) refl
original-data-beta-goal-safe : R.C.Sound.SafeState Existing.value (N.Request.goal data-beta-query)
original-data-beta-goal-safe = R.Checked.trace-safe data-beta-checked ⇝*-refl
signature-free-data-still-inconclusive : Compare.compare 64 0 [] Existing.goal (N.Request.goal data-beta-query)
  ≡ Compare.unknown Compare.left-side E.unsupported
signature-free-data-still-inconclusive = refl

exact-atom-zero-budget : N.present (R.verify 0 (record query { goal = tm-atom_type ; goal-kind-recipe = r-leaf })) ≡ true
exact-atom-zero-budget = refl
beta-needs-budget : R.verify 0 query ≡ N.rejected (N.inconclusive Compare.left-side E.exhausted)
beta-needs-budget = refl
wrong-goal : N.present (R.verify 64 (record query { goal = tm-float_type ; goal-kind-recipe = r-leaf })) ≡ false
wrong-goal = refl
wrong-inferred-kind : R.verify 64 (record query { inferred-kind-recipe = r-lam r-leaf r-leaf })
  ≡ N.rejected N.inferred-kind-failed
wrong-inferred-kind = refl
non-kind-goal : R.verify 64 (record query { goal = tm-atom_lit "payload" ; goal-kind-recipe = r-leaf })
  ≡ N.rejected N.goal-kind-failed
non-kind-goal = refl
universe-ceiling : N.present (R.verify 64 (record query { goal = tm-type l2 ; goal-kind-recipe = r-leaf })) ≡ false
universe-ceiling = refl
wrong-grade : N.present (R.verify 64 (record lambda-query
  { goal = tm-pi linear tm-atom_type tm-atom_type ; goal-kind-recipe = r-pi r-leaf r-leaf })) ≡ false
wrong-grade = refl
cumulative-query : N.Request
cumulative-query = N.request tm-atom_type r-leaf r-leaf (tm-type l1) r-leaf
cumulativity-is-not-conversion : N.present (R.verify 64 cumulative-query) ≡ false
cumulativity-is-not-conversion = refl
explicit-cumulativity-still-works : N.present
  (R.verify 0 (record cumulative-query { subject-recipe = r-cumul l1 r-leaf })) ≡ true
explicit-cumulativity-still-works = refl
escaped-subject : R.verify 64 (record query { subject = tm-var 0 }) ≡ N.rejected N.unsupported-subject
escaped-subject = refl
forged-subject-recipe : R.verify 64 (record query { subject-recipe = r-app r-leaf r-leaf })
  ≡ N.rejected N.inference-failed
forged-subject-recipe = refl
malformed-characters : Chars.verify 64 ('(' ∷ []) ≡ N.rejected N.malformed-wire
malformed-characters = refl
trailing-characters : N.present (Chars.verify 64 (Produced.characters ++ (';' ∷ []))) ≡ false
trailing-characters = refl
wrong-tag : Wire.from-node Bundle.table (Tags.tagged 19 []) ≡ nothing
wrong-tag = refl
missing-name : Wire.to-node [] query ≡ nothing
missing-name = refl
