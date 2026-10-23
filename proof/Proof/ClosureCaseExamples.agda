{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Fixed actual observations, positive native traces and negative MODEL
-- controls. Successful execution is NOT declaration/coverage validation.
------------------------------------------------------------------------
module Proof.ClosureCaseExamples where

import Data.Bool

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Reduction using (_⇝*_)
open import Core.NativeRecipe using (scope?)
open import Core.Signature using (just-inj)
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick)
import Core.ClosureEval as E
import Core.ClosureCase as Case
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Proof.ClosureCase as Model
import Proof.ClosureCaseSafety as Safety
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotationExamples as Quotation
import Proof.CallerAdmissionExamples as Admitted
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableCase as Observed
module C = Admitted.R.C
module Simulation = Model.Simulation C.W.sig
module Safe = Safety.Safe Source.Pin.admission

result-value : ∀ {A : E.Value → Set} → Case.Result (Σ E.Value A) → Maybe E.Value
result-value (Case.stop reason) = nothing
result-value (Case.done (value , evidence)) = just value
extract : ∀ {A : E.Value → Set} (result : Case.Result (Σ E.Value A)) value
  → result-value result ≡ just value → A value
extract (Case.stop reason) value ()
extract (Case.done (actual , evidence)) value found with just-inj found
... | refl = evidence

module Observation (program : Term) (environment : List E.Value) (value : E.Value) (quoted : Term)
  (evaluated : result-value (Case.run 32 program environment) ≡ just value)
  (readback : Quotation.term-result (Q.run 64 0 value) ≡ just quoted)
  (scoped : present (scope? (length environment) program) ≡ Data.Bool.true) where
  execution : Case.Executes environment program value
  execution = extract (Case.run 32 program environment) value evaluated
  module Readback = Quotation.Quoted 0 value quoted readback
  path : ∀ {terms} → Scope.EnvironmentScoped 0 environment → Meaning.Environments 0 environment terms
    → _⇝*_ C.W.sig (substS (Meaning.environment-sub terms) program) quoted
  path scope env = Simulation.quotation scope (pick (scope? (length environment) program) scoped)
    env execution Readback.evidence

module Unpack = Observation Observed.unpack-program Observed.unpack-environment
  Observed.unpack-value Observed.unpack-quoted refl refl refl
module Last = Observation Observed.last-program Observed.last-environment
  Observed.last-value Observed.last-quoted refl refl refl
module First = Observation Observed.first-program Observed.first-environment
  Observed.first-value Observed.first-quoted refl refl refl
module Outer = Observation Observed.outer-program Observed.outer-environment
  Observed.outer-value Observed.outer-quoted refl refl refl
module Nested = Observation Observed.nested-program Observed.nested-environment
  Observed.nested-value Observed.nested-quoted refl refl refl
module NestedOuter = Observation Observed.nested-outer-program Observed.nested-outer-environment
  Observed.nested-outer-value Observed.nested-outer-quoted refl refl refl
module Zero = Observation Observed.zero-program Observed.zero-environment
  Observed.zero-value Observed.zero-quoted refl refl refl
module Redex = Observation Observed.redex-program Observed.redex-environment
  Observed.redex-value Observed.redex-quoted refl refl refl
module Duplicate = Observation Observed.duplicate-program Observed.duplicate-environment
  Observed.duplicate-value Observed.duplicate-quoted refl refl refl
module Skipped = Observation Observed.skipped-program Observed.skipped-environment
  Observed.skipped-value Observed.skipped-quoted refl refl refl
module InertMotive = Observation Observed.inert-motive-program Observed.inert-motive-environment
  Observed.inert-motive-value Observed.inert-motive-quoted refl refl refl

unpack-path : _⇝*_ C.W.sig Observed.unpack-program Observed.unpack-quoted
unpack-path = Unpack.path Scope.s[] Meaning.d[]
first-path : _⇝*_ C.W.sig Observed.first-program Observed.first-quoted
first-path = First.path Scope.s[] Meaning.d[]
last-path : _⇝*_ C.W.sig Observed.last-program Observed.last-quoted
last-path = Last.path Scope.s[] Meaning.d[]
nested-path : _⇝*_ C.W.sig Observed.nested-program Observed.nested-quoted
nested-path = Nested.path Scope.s[] Meaning.d[]
redex-path : _⇝*_ C.W.sig Observed.redex-program Observed.redex-quoted
redex-path = Redex.path Scope.s[] Meaning.d[]
outer-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (tm-atom_lit "hidden" ∷ [])) Observed.outer-program) Observed.outer-quoted
outer-path = Outer.path (Scope.s∷ Scope.s-atom Scope.s[])
  (Meaning.d∷ Meaning.d-atom Meaning.d[])
nested-outer-path : _⇝*_ C.W.sig
  (substS (Meaning.environment-sub (tm-atom_lit "hidden" ∷ [])) Observed.nested-outer-program)
  Observed.nested-outer-quoted
nested-outer-path = NestedOuter.path (Scope.s∷ Scope.s-atom Scope.s[])
  (Meaning.d∷ Meaning.d-atom Meaning.d[])
-- Heterogeneous fields distinguish correct order; a last-field-at-one
-- implementation cannot satisfy both observations.
first-not-last : Observed.first-quoted ≢ Observed.last-quoted
first-not-last ()
duplicate-selects-first : Observed.duplicate-quoted ≡ Observed.first-quoted
duplicate-selects-first = refl

unpack-safe : C.Sound.SafeState Observed.unpack-quoted tm-atom_type
unpack-safe = proj₂ (Safe.safe-quotation Admitted.empty-case-checked Unpack.execution Unpack.Readback.evidence)
unpack-value-safe : C.Sound.SafeState Observed.unpack-quoted tm-atom_type
unpack-value-safe = proj₂ (proj₂ (Safe.safe-execution Admitted.empty-case-checked Unpack.execution))
checked-run : result-value (Safe.run-safe 32 Admitted.empty-case-checked) ≡ just Observed.unpack-value
checked-run = refl

failure : ∀ {A} → Case.Result A → Maybe Case.Failure
failure (Case.done result) = nothing
failure (Case.stop reason) = just reason
zero-budget : failure (Case.run 0 Observed.unpack-program []) ≡ just Case.exhausted
zero-budget = refl
field-budget : failure (Case.run 1 Observed.unpack-program []) ≡ just Case.exhausted
field-budget = refl
filtered-not-modelled : failure (Case.run 32 Observed.filtered-program []) ≡ just Case.arity-mismatch
filtered-not-modelled = refl
erased-not-modelled : failure (Case.run 32 Observed.erased-program []) ≡ just Case.arity-mismatch
erased-not-modelled = refl
-- The generated actual results are nevertheless ordinary payloads.
actual-filtered : Observed.filtered-quoted ≡ Observed.last-quoted
actual-filtered = refl
actual-erased : Observed.erased-quoted ≡ Observed.last-quoted
actual-erased = refl

payload : Term
payload = tm-atom_lit "payload"
case-term : List Term → List Branch → Term
case-term args branches = tm-case (tm-ctor "Boundary#Pack" args) tm-atom_type branches
missing-branch : failure (Case.run 16 (case-term [] []) []) ≡ just Case.missing-branch
missing-branch = refl
foreign-name : failure (Case.run 16 (case-term [] (("Boundary#Alternate" , 0 , payload) ∷ [])) [])
  ≡ just Case.missing-branch
foreign-name = refl
first-arity-not-skipped : failure (Case.run 16
  (case-term [] (("Boundary#Pack" , 1 , payload) ∷ ("Boundary#Pack" , 0 , payload) ∷ [])) [])
  ≡ just Case.arity-mismatch
first-arity-not-skipped = refl
unbound-field : failure (Case.run 16
  (case-term (tm-var 0 ∷ []) (("Boundary#Pack" , 1 , payload) ∷ [])) [])
  ≡ just (Case.field-failure E.unbound)
unbound-field = refl
unbound-body : failure (Case.run 16
  (case-term [] (("Boundary#Pack" , 0 , tm-var 0) ∷ [])) []) ≡ just (Case.body-failure E.unbound)
unbound-body = refl
unsupported-field : failure (Case.run 16
  (case-term (tm-data "Boundary#Packed" [] [] ∷ []) (("Boundary#Pack" , 1 , payload) ∷ [])) [])
  ≡ just (Case.field-failure E.unsupported)
unsupported-field = refl
fields-before-lookup : failure (Case.run 16 (case-term (tm-var 0 ∷ []) []) [])
  ≡ just (Case.field-failure E.unbound)
fields-before-lookup = refl
non-function-body : failure (Case.run 16
  (case-term [] (("Boundary#Pack" , 0 , tm-app tm-atom_type payload) ∷ [])) [])
  ≡ just (Case.body-failure E.non-function)
non-function-body = refl
recursive-case-body-not-modelled : failure (Case.run 16
  (case-term [] (("Boundary#Pack" , 0 , Observed.zero-program) ∷ [])) [])
  ≡ just (Case.body-failure E.unsupported)
recursive-case-body-not-modelled = refl
neutral-case-not-modelled : failure (Case.run 16
  (tm-case (tm-var 0) tm-atom_type []) (E.v-neutral (E.n-var 0) ∷ [])) ≡ just Case.unsupported-head
neutral-case-not-modelled = refl
computed-scrutinee-not-modelled : failure (Case.run 16
  (tm-case (tm-let unrestricted tm-atom_type payload (tm-var 0)) tm-atom_type []) [])
  ≡ just Case.unsupported-head
computed-scrutinee-not-modelled = refl
compact-not-modelled : failure (Case.run 16 (tm-case (tm-nat_lit 0) tm-atom_type []) [])
  ≡ just Case.unsupported-head
compact-not-modelled = refl

-- Only the total fuelled MODEL sees this term, never actual unbounded Eval.
omega : Term
omega = tm-app self self
  where self = tm-lam unrestricted tm-atom_type (tm-app (tm-var 0) (tm-var 0))
unused-field-still-eager : failure (Case.run 16
  (case-term (omega ∷ []) (("Boundary#Pack" , 1 , payload) ∷ [])) [])
  ≡ just (Case.field-failure E.exhausted)
unused-field-still-eager = refl
selected-body-budget : failure (Case.run 16
  (case-term [] (("Boundary#Pack" , 0 , omega) ∷ [])) [])
  ≡ just (Case.body-failure E.exhausted)
selected-body-budget = refl

-- A successful raw zero-field branch does not validate the registered
-- two-field declaration or the native dependent-motive/coverage contract.
zero-not-admitted : present (Admitted.R.verify
  (record Admitted.empty-case-query { subject = Observed.zero-program })) ≡ Data.Bool.false
zero-not-admitted = refl
inert-motive-not-admitted : present (Admitted.R.verify
  (record Admitted.empty-case-query { subject = Observed.inert-motive-program }))
  ≡ Data.Bool.false
inert-motive-not-admitted = refl
