{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Evaluated exact-case observations, native safety and explicit exclusions.
-- Raw positive execution is not a coverage/motive/admission certificate.
------------------------------------------------------------------------
module Proof.EvaluatedCaseExamples where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Data.Product using (proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.NativeRecipe
open import Core.Reduction using (_⇝*_)
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ClosureCase as Case
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.CallerAdmission as Caller
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureCase as Model
import Proof.ClosureCaseExamples as Previous
import Proof.ClosureEvaluationExamples as Closure
import Proof.NativeRecipeExamples as Recipes
import Fixtures.ExecutableScrutinee as Observed
import Fixtures.ExecutableCase as Old
module C = Previous.C
module Simulation = Model.Simulation C.W.sig
module Safe = Previous.Safe

module Beta = Previous.Observation Observed.beta-program Observed.beta-environment
  Observed.beta-value Observed.beta-quoted refl refl refl
module Zeta = Previous.Observation Observed.zeta-program Observed.zeta-environment
  Observed.zeta-value Observed.zeta-quoted refl refl refl
module Eager = Previous.Observation Observed.eager-program Observed.eager-environment
  Observed.eager-value Observed.eager-quoted refl refl refl
module Variable = Previous.Observation Observed.variable-program Observed.variable-environment
  Observed.variable-value Observed.variable-quoted refl refl refl
module Outer = Previous.Observation Observed.outer-program Observed.outer-environment
  Observed.outer-value Observed.outer-quoted refl refl refl
module Capture = Previous.Observation Observed.capture-program Observed.capture-environment
  Observed.capture-value Observed.capture-quoted refl refl refl
module Nested = Previous.Observation Observed.nested-program Observed.nested-environment
  Observed.nested-value Observed.nested-quoted refl refl refl
module Skipped = Previous.Observation Observed.skipped-program Observed.skipped-environment
  Observed.skipped-value Observed.skipped-quoted refl refl refl
module InertMotive = Previous.Observation Observed.inert-motive-program Observed.inert-motive-environment
  Observed.inert-motive-value Observed.inert-motive-quoted refl refl refl
module Zero = Previous.Observation Observed.zero-program Observed.zero-environment
  Observed.zero-value Observed.zero-quoted refl refl refl

beta-path : _⇝*_ C.W.sig Observed.beta-program Observed.beta-quoted
beta-path = Beta.path Scope.s[] Meaning.d[]
zeta-path : _⇝*_ C.W.sig Observed.zeta-program Observed.zeta-quoted
zeta-path = Zeta.path Scope.s[] Meaning.d[]
capture-path : _⇝*_ C.W.sig Observed.capture-program Observed.capture-quoted
capture-path = Capture.path Scope.s[] Meaning.d[]
nested-path : _⇝*_ C.W.sig Observed.nested-program Observed.nested-quoted
nested-path = Nested.path Scope.s[] Meaning.d[]
packed : Term
packed = tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
packed-denotation : Meaning.Denotes 0
  (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ E.v-atom "payload" ∷ [])) packed
packed-denotation = Meaning.d-ctor (Meaning.d∷ Meaning.d-atom-type (Meaning.d∷ Meaning.d-atom Meaning.d[]))
packed-scope : Scope.ValueScoped 0 (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ E.v-atom "payload" ∷ []))
packed-scope = Scope.s-ctor (Scope.s∷ Scope.s-atom-type (Scope.s∷ Scope.s-atom Scope.s[]))
variable-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (packed ∷ [])) Observed.variable-program) Observed.variable-quoted
variable-path = Variable.path (Scope.s∷ packed-scope Scope.s[]) (Meaning.d∷ packed-denotation Meaning.d[])
outer-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (tm-atom_lit "hidden" ∷ packed ∷ [])) Observed.outer-program)
  Observed.outer-quoted
outer-path = Outer.path (Scope.s∷ Scope.s-atom (Scope.s∷ packed-scope Scope.s[]))
  (Meaning.d∷ Meaning.d-atom (Meaning.d∷ packed-denotation Meaning.d[]))

scrutinee : Term → Term
scrutinee (tm-case scrutinee motive branches) = scrutinee
scrutinee other = other
data-kind : Recipe
data-kind = r-data [] (r-leaf ∷ [])
ctor-recipe : Recipe
ctor-recipe = r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])
case-recipe : Recipe → Recipe
case-recipe scrutinee-recipe =
  r-case scrutinee-recipe [] (r-leaf ∷ []) l0 Recipes.case-kind-recipe Recipes.case-motive-recipe
    Recipes.unpack-case-branches
-- Reconstruct the conversion at the NEW scrutinee syntax; do not reuse
-- the old unpack's asserted middle term or treat evaluation as typing.
native-recipe : Term → Recipe → Recipe
native-recipe program scrutinee-recipe = r-convert tm-atom_type
  (c-trans (tm-app
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])) tm-atom_type)
    (scrutinee program)) (c-app c-beta c-refl) c-beta) (case-recipe scrutinee-recipe)
beta-scrutinee-recipe : Recipe
beta-scrutinee-recipe = r-app (r-lam r-leaf ctor-recipe) r-leaf
zeta-scrutinee-recipe : Recipe
zeta-scrutinee-recipe = r-let data-kind ctor-recipe r-leaf
eager-scrutinee-recipe : Recipe
eager-scrutinee-recipe = r-app (r-lam r-leaf ctor-recipe) (r-app (r-lam r-leaf r-leaf) r-leaf)

module BetaNative = Closure.Native Observed.beta-program tm-atom_type
  (native-recipe Observed.beta-program beta-scrutinee-recipe) r-leaf refl
module ZetaNative = Closure.Native Observed.zeta-program tm-atom_type
  (native-recipe Observed.zeta-program zeta-scrutinee-recipe) r-leaf refl
module EagerNative = Closure.Native Observed.eager-program tm-atom_type
  (native-recipe Observed.eager-program eager-scrutinee-recipe) r-leaf refl
beta-safe : C.Sound.SafeState Observed.beta-quoted tm-atom_type
beta-safe = proj₂ (Safe.safe-quotation BetaNative.admitted Beta.execution Beta.Readback.evidence)
zeta-safe : C.Sound.SafeState Observed.zeta-quoted tm-atom_type
zeta-safe = proj₂ (Safe.safe-quotation ZetaNative.admitted Zeta.execution Zeta.Readback.evidence)
eager-safe : C.Sound.SafeState Observed.eager-quoted tm-atom_type
eager-safe = proj₂ (Safe.safe-quotation EagerNative.admitted Eager.execution Eager.Readback.evidence)
beta-safe-run : Previous.result-value (Safe.run-safe 32 BetaNative.admitted) ≡ just Observed.beta-value
beta-safe-run = refl

-- Transform positive direct evidence explicitly. No proof equality or
-- same-budget equivalence of the two evaluators is assumed.
bridged-direct-path : _⇝*_ C.W.sig Old.unpack-program Old.unpack-quoted
bridged-direct-path = Simulation.quotation Scope.s[] (pick (scope? 0 Old.unpack-program) refl)
  Meaning.d[] (Case.as-computed Previous.Unpack.execution) Previous.Unpack.Readback.evidence
bridge-selects-evaluated-route : Case.route (Case.as-computed Previous.Unpack.execution) ≡ Case.evaluated-route
bridge-selects-evaluated-route = Case.as-computed-route Previous.Unpack.execution
direct-value : Previous.result-value (Case.run 2 Old.zero-program []) ≡ just Old.zero-value
direct-value = refl
computed-needs-more-budget : Previous.failure
  (Case.run-computed 2 (tm-ctor "Boundary#Pack" []) tm-atom_type (("Boundary#Pack" , 0 , tm-atom_lit "payload") ∷ []) [])
  ≡ just (Case.scrutinee-failure E.exhausted)
computed-needs-more-budget = refl
zero-budget : Previous.failure (Case.run 0 Observed.beta-program []) ≡ just Case.exhausted
zero-budget = refl
scrutinee-budget : Previous.failure (Case.run 1 Observed.beta-program []) ≡ just (Case.scrutinee-failure E.exhausted)
scrutinee-budget = refl

-- Actual Eval preserves neutral cases and canonicalises broader layouts.
-- The exact adapter intentionally does neither.
neutral-rejected : Previous.failure (Case.run 32 Observed.neutral-program []) ≡ just Case.neutral-scrutinee
neutral-rejected = refl
actual-neutral-readback : Observed.neutral-actual-quoted ≡ Observed.neutral-program
actual-neutral-readback = refl
filtered-rejected : Previous.failure (Case.run 32 Observed.filtered-program []) ≡ just Case.arity-mismatch
filtered-rejected = refl
erased-rejected : Previous.failure (Case.run 32 Observed.erased-program []) ≡ just Case.arity-mismatch
erased-rejected = refl
actual-filtered-payload : Observed.filtered-actual-quoted ≡ tm-atom_lit "payload"
actual-filtered-payload = refl
actual-erased-payload : Observed.erased-actual-quoted ≡ tm-atom_lit "payload"
actual-erased-payload = refl

wrap : Term → List Branch → Term
wrap term branches = tm-case (tm-let unrestricted tm-atom_type term (tm-var 0)) tm-atom_type branches
payload : Term
payload = tm-atom_lit "payload"
empty-ctor : Term
empty-ctor = tm-ctor "Boundary#Pack" []
singleton : Term → List Branch
singleton body = ("Boundary#Pack" , 0 , body) ∷ []
missing : Previous.failure (Case.run 16 (wrap empty-ctor []) []) ≡ just Case.missing-branch
missing = refl
first-wrong-arity : Previous.failure (Case.run 16
  (wrap empty-ctor (("Boundary#Pack" , 1 , payload) ∷ singleton payload)) []) ≡ just Case.arity-mismatch
first-wrong-arity = refl
scrutinee-before-lookup : Previous.failure (Case.run 16 (wrap (tm-var 0) []) [])
  ≡ just (Case.scrutinee-failure E.unbound)
scrutinee-before-lookup = refl
non-function-scrutinee : Previous.failure (Case.run 16 (wrap (tm-app tm-atom_type payload) []) [])
  ≡ just (Case.scrutinee-failure E.non-function)
non-function-scrutinee = refl
non-constructor : Previous.failure (Case.run 16 (wrap payload []) []) ≡ just Case.non-constructor
non-constructor = refl
closure-not-constructor : Previous.failure (Case.run 16
  (wrap (tm-lam unrestricted tm-atom_type (tm-var 0)) []) []) ≡ just Case.non-constructor
closure-not-constructor = refl
unsupported-data : Previous.failure (Case.run 16 (wrap (tm-data "Boundary#Packed" [] []) []) [])
  ≡ just (Case.scrutinee-failure E.unsupported)
unsupported-data = refl
unbound-body : Previous.failure (Case.run 16 (wrap empty-ctor (singleton (tm-var 0))) [])
  ≡ just (Case.body-failure E.unbound)
unbound-body = refl
case-in-scrutinee-not-modelled : Previous.failure (Case.run 16 (wrap Old.zero-program []) [])
  ≡ just (Case.scrutinee-failure E.unsupported)
case-in-scrutinee-not-modelled = refl
case-in-body-not-modelled : Previous.failure (Case.run 16 (wrap empty-ctor (singleton Old.zero-program)) [])
  ≡ just (Case.body-failure E.unsupported)
case-in-body-not-modelled = refl
omega-budget : Previous.failure (Case.run 16 (wrap Closure.omega []) [])
  ≡ just (Case.scrutinee-failure E.exhausted)
omega-budget = refl
body-omega-budget : Previous.failure (Case.run 16 (wrap empty-ctor (singleton Closure.omega)) [])
  ≡ just (Case.body-failure E.exhausted)
body-omega-budget = refl
-- Core Eval and its normalizer still reject case syntax; the extension is
-- intentionally isolated in this adapter.
core-evaluator-unchanged : Closure.failure (E.run 64 Observed.beta-program []) ≡ just E.unsupported
core-evaluator-unchanged = refl
core-normalizer-unchanged : Closure.failure (Q.normalise 64 0 Observed.beta-program []) ≡ just E.unsupported
core-normalizer-unchanged = refl
inert-motive-not-admitted : present (Closure.CallerReplay.verify
  (Caller.request [] [] [] [] Observed.inert-motive-program tm-atom_type
    (native-recipe Observed.inert-motive-program zeta-scrutinee-recipe) r-leaf)) ≡ false
inert-motive-not-admitted = refl
