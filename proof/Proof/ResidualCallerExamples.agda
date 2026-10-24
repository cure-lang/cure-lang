{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Open conversion precedes coherent closure. Literal packet/data
-- observations are independently replayed, not trusted context proofs.
------------------------------------------------------------------------
module Proof.ResidualCallerExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Core.Syntax
open import Core.Universe using (l0; l2)
open import Core.Grade using (unrestricted)
open import Core.Typing using (⟨⟩)
open import Core.NativeRecipe
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (_⇝*_; ⇝*-refl)
open import Proof.CheckedAdmissionExamples using (pick; pick-equation)
import Core.AmbientResidualAdmission as Ambient
import Core.ResidualCallerAdmission as Caller
import Core.CallerAdmission as OldCaller
import Core.WireResidualCaller as Wire
import Core.WireCaller as OldWire
import Core.WireRecipe as RecipeWire
import Core.ResidualComparison as Compare
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.LocalFrame as Frame
import Proof.FreshEnvironment as Fresh
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quotation
import Proof.ClosureQuotationExamples as Quote
import Proof.ResidualComparisonExamples as Comparison
import Proof.Substitution as Substitution
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableBundle as Bundle
import Fixtures.ExecutableResidualCaller as Produced
module R = Caller.Replay Source.Pin.admission
module Chars = Wire.Replay Source.Pin.admission 64
module Old = OldCaller.Replay Source.Pin.admission
module Model = Quotation.Simulation R.C.W.sig

query-of : (cc kc : List Char) → present (Wire.decode Bundle.table cc kc) ≡ true → Caller.Request
query-of cc kc parsed = pick (Wire.decode Bundle.table cc kc) parsed
is-normalized : ∀ {size left right} → Ambient.Basis size left right → Bool
is-normalized (Ambient.exact same) = false
is-normalized (Ambient.normalized equal) = true

module Example (cc kc : List Char) (parsed : present (Wire.decode Bundle.table cc kc) ≡ true)
  (accepted : present (R.verify 64 (query-of cc kc parsed)) ≡ true) (output : Term)
  (quoted : Quote.term-result (Q.normalise-residual-with R.C.W.ind 64 0
    (R.Checked.closed-subject (pick (R.verify 64 (query-of cc kc parsed)) accepted)) []) ≡ just output) where
  query : Caller.Request
  query = query-of cc kc parsed
  decoded : Wire.decode Bundle.table cc kc ≡ just query
  decoded = pick-equation (Wire.decode Bundle.table cc kc) parsed
  wire-positive : present (Chars.verify cc kc) ≡ true
  wire-positive = trans (Chars.verify-decoded cc kc query decoded) accepted
  wire-checked : Chars.Checked cc kc
  wire-checked = pick (Chars.verify cc kc) wire-positive
  checked : R.Checked query
  checked = Chars.pin wire-checked query decoded
  safe : R.C.Sound.SafeState (R.Checked.closed-subject checked) (R.Checked.closed-goal checked)
  safe = R.Checked.trace-safe checked ⇝*-refl
  readback : Q.ResidualNormalizes 0 [] (R.Checked.closed-subject checked) output
  readback = Quote.extract (Q.normalise-residual-with R.C.W.ind 64 0 (R.Checked.closed-subject checked) []) output quoted
  path : _⇝*_ R.C.W.sig (R.Checked.closed-subject checked) output
  path = Model.O.⇝*-trans
    (Model.Eval.equal-path (sym (Substitution.substS-idSub (R.Checked.closed-subject checked))))
    (Model.residual-normalization Scope.s[] (R.Original.Sc.infer-scoped (R.Checked.closed-typed checked)) Meaning.d[] readback)
  readback-safe : R.C.Sound.SafeState output (R.Checked.closed-goal checked)
  readback-safe = R.Checked.trace-safe checked path
  budgets-agree : ∀ budget → R.Checked.run checked budget ≡ R.C.Sound.truncate budget (R.Checked.tree checked)
  budgets-agree = R.Checked.budgets-agree checked

module Dependent = Example Produced.dependent-caller-characters Produced.dependent-kind-characters refl refl
  Produced.dependent-closed-quoted refl
module Binder = Example Produced.binder-caller-characters Produced.binder-kind-characters refl refl
  Produced.binder-closed-quoted refl
module OpaqueCase = Example Produced.opaque-caller-characters Produced.opaque-kind-characters refl refl
  Produced.opaque-closed-quoted refl
module ConstructorCase = Example Produced.constructor-caller-characters Produced.constructor-kind-characters refl refl
  Produced.constructor-closed-quoted refl
module Nested = Example Produced.nested-caller-characters Produced.nested-kind-characters refl refl
  Produced.nested-closed-quoted refl
module Empty = Example Produced.empty-caller-characters Produced.empty-kind-characters refl refl
  Produced.empty-closed-quoted refl

module Observation (cc kc : List Char) (parsed : present (Wire.decode Bundle.table cc kc) ≡ true)
  (size : ℕ) (env : List E.Value) (inferred lq rq : Term) (actual : Bool)
  (fresh-agrees : Fresh.environment size ≡ env)
  (left-agrees : Quote.term-result (Q.normalise-residual-with R.C.W.ind 64 size inferred env) ≡ just lq)
  (right-agrees : Quote.term-result (Q.normalise-residual-with R.C.W.ind 64 size
    (OldCaller.Request.goal (Caller.Request.caller (query-of cc kc parsed))) env) ≡ just rq)
  (classified : Compare.classify (Compare.compare-with R.C.W.ind 64 size env inferred
    (OldCaller.Request.goal (Caller.Request.caller (query-of cc kc parsed)))) ≡ Compare.equal-forms)
  (left-scoped : present (scope? (Data.List.length env) inferred) ≡ true)
  (right-scoped : present (scope? (Data.List.length env)
    (OldCaller.Request.goal (Caller.Request.caller (query-of cc kc parsed)))) ≡ true)
  (actual-positive : actual ≡ true) where
  module Replay = Comparison.Observation size env inferred
    (OldCaller.Request.goal (Caller.Request.caller (query-of cc kc parsed))) lq rq Compare.equal-forms
    left-agrees right-agrees classified left-scoped right-scoped
  module Equal = Comparison.Positive size env inferred
    (OldCaller.Request.goal (Caller.Request.caller (query-of cc kc parsed)))
    classified left-scoped right-scoped actual actual-positive

-- Literal open observation instances.

module ObservedDependent = Observation Produced.dependent-caller-characters Produced.dependent-kind-characters refl
  Produced.dependent-size Produced.dependent-environment Produced.dependent-inferred Produced.dependent-open-left Produced.dependent-open-right
  Produced.dependent-actual refl refl refl refl refl refl refl
dependent-size : R.Checked.size Dependent.checked ≡ Produced.dependent-size
dependent-size = refl
dependent-encoded : Wire.encode Bundle.table Dependent.query
  ≡ just (Produced.dependent-caller-characters , Produced.dependent-kind-characters)
dependent-encoded = refl
module ObservedBinder = Observation Produced.binder-caller-characters Produced.binder-kind-characters refl
  Produced.binder-size Produced.binder-environment Produced.binder-inferred Produced.binder-open-left Produced.binder-open-right
  Produced.binder-actual refl refl refl refl refl refl refl
binder-size : R.Checked.size Binder.checked ≡ Produced.binder-size
binder-size = refl
binder-encoded : Wire.encode Bundle.table Binder.query
  ≡ just (Produced.binder-caller-characters , Produced.binder-kind-characters)
binder-encoded = refl
module ObservedOpaqueCase = Observation Produced.opaque-caller-characters Produced.opaque-kind-characters refl
  Produced.opaque-size Produced.opaque-environment Produced.opaque-inferred Produced.opaque-open-left Produced.opaque-open-right
  Produced.opaque-actual refl refl refl refl refl refl refl
opaquecase-size : R.Checked.size OpaqueCase.checked ≡ Produced.opaque-size
opaquecase-size = refl
opaquecase-encoded : Wire.encode Bundle.table OpaqueCase.query
  ≡ just (Produced.opaque-caller-characters , Produced.opaque-kind-characters)
opaquecase-encoded = refl
module ObservedConstructorCase = Observation Produced.constructor-caller-characters Produced.constructor-kind-characters refl
  Produced.constructor-size Produced.constructor-environment Produced.constructor-inferred Produced.constructor-open-left Produced.constructor-open-right
  Produced.constructor-actual refl refl refl refl refl refl refl
constructorcase-size : R.Checked.size ConstructorCase.checked ≡ Produced.constructor-size
constructorcase-size = refl
constructorcase-encoded : Wire.encode Bundle.table ConstructorCase.query
  ≡ just (Produced.constructor-caller-characters , Produced.constructor-kind-characters)
constructorcase-encoded = refl
module ObservedNested = Observation Produced.nested-caller-characters Produced.nested-kind-characters refl
  Produced.nested-size Produced.nested-environment Produced.nested-inferred Produced.nested-open-left Produced.nested-open-right
  Produced.nested-actual refl refl refl refl refl refl refl
nested-size : R.Checked.size Nested.checked ≡ Produced.nested-size
nested-size = refl
nested-encoded : Wire.encode Bundle.table Nested.query
  ≡ just (Produced.nested-caller-characters , Produced.nested-kind-characters)
nested-encoded = refl
module ObservedEmpty = Observation Produced.empty-caller-characters Produced.empty-kind-characters refl
  Produced.empty-size Produced.empty-environment Produced.empty-inferred Produced.empty-open-left Produced.empty-open-right
  Produced.empty-actual refl refl refl refl refl refl refl
empty-size : R.Checked.size Empty.checked ≡ Produced.empty-size
empty-size = refl
empty-encoded : Wire.encode Bundle.table Empty.query
  ≡ just (Produced.empty-caller-characters , Produced.empty-kind-characters)
empty-encoded = refl

-- Actual inferred types, not assertions supplied by the caller packet.
dependent-inferred : R.Open.Checked.inferred (R.Checked.open-checked Dependent.checked) ≡ Produced.dependent-inferred
dependent-inferred = refl
binder-inferred : R.Open.Checked.inferred (R.Checked.open-checked Binder.checked) ≡ Produced.binder-inferred
binder-inferred = refl
opaque-inferred : R.Open.Checked.inferred (R.Checked.open-checked OpaqueCase.checked) ≡ Produced.opaque-inferred
opaque-inferred = refl
constructor-inferred : R.Open.Checked.inferred (R.Checked.open-checked ConstructorCase.checked) ≡ Produced.constructor-inferred
constructor-inferred = refl
nested-inferred : R.Open.Checked.inferred (R.Checked.open-checked Nested.checked) ≡ Produced.nested-inferred
nested-inferred = refl
empty-inferred : R.Open.Checked.inferred (R.Checked.open-checked Empty.checked) ≡ Produced.empty-inferred
empty-inferred = refl

dependent-normalized : is-normalized (R.Open.Checked.basis (R.Checked.open-checked Dependent.checked)) ≡ true
dependent-normalized = refl
binder-normalized : is-normalized (R.Open.Checked.basis (R.Checked.open-checked Binder.checked)) ≡ true
binder-normalized = refl
opaque-normalized : is-normalized (R.Open.Checked.basis (R.Checked.open-checked OpaqueCase.checked)) ≡ true
opaque-normalized = refl
constructor-normalized : is-normalized (R.Open.Checked.basis (R.Checked.open-checked ConstructorCase.checked)) ≡ true
constructor-normalized = refl
nested-normalized : is-normalized (R.Open.Checked.basis (R.Checked.open-checked Nested.checked)) ≡ true
nested-normalized = refl
empty-normalized : is-normalized (R.Open.Checked.basis (R.Checked.open-checked Empty.checked)) ≡ true
empty-normalized = refl

-- Closing equality is checked against actual observations, not invented reducts.
dependent-closed : R.Checked.closed-subject Dependent.checked ≡ Produced.dependent-closed-subject
dependent-closed = refl
dependent-goal : R.Checked.closed-goal Dependent.checked ≡ Produced.dependent-closed-goal
dependent-goal = refl
binder-closed : R.Checked.closed-subject Binder.checked ≡ Produced.binder-closed-subject
binder-closed = refl
binder-goal : R.Checked.closed-goal Binder.checked ≡ Produced.binder-closed-goal
binder-goal = refl
opaque-closed : R.Checked.closed-subject OpaqueCase.checked ≡ Produced.opaque-closed-subject
opaque-closed = refl
opaque-goal : R.Checked.closed-goal OpaqueCase.checked ≡ Produced.opaque-closed-goal
opaque-goal = refl
constructor-closed : R.Checked.closed-subject ConstructorCase.checked ≡ Produced.constructor-closed-subject
constructor-closed = refl
constructor-goal : R.Checked.closed-goal ConstructorCase.checked ≡ Produced.constructor-closed-goal
constructor-goal = refl
nested-closed : R.Checked.closed-subject Nested.checked ≡ Produced.nested-closed-subject
nested-closed = refl
nested-goal : R.Checked.closed-goal Nested.checked ≡ Produced.nested-closed-goal
nested-goal = refl
empty-closed : R.Checked.closed-subject Empty.checked ≡ Produced.empty-closed-subject
empty-closed = refl
empty-goal : R.Checked.closed-goal Empty.checked ≡ Produced.empty-closed-goal
empty-goal = refl

with-call : Caller.Request → OldCaller.Request → Caller.Request
with-call query call = Caller.request call (Caller.Request.inferred-kind-recipe query)
dependent-call : OldCaller.Request
dependent-call = Caller.Request.caller Dependent.query
exact-query : Caller.Request
exact-query = with-call Dependent.query (record dependent-call { goal = Produced.dependent-inferred ; goal-recipe = r-leaf })
exact-checked : R.Checked exact-query
exact-checked = pick (R.verify 0 exact-query) refl
exact-zero : present (R.verify 0 exact-query) ≡ true
exact-zero = refl
nonexact-budget : present (R.verify 0 Dependent.query) ≡ false
nonexact-budget = refl
strict-caller-unchanged : present (Old.verify dependent-call) ≡ false
strict-caller-unchanged = refl
module OldChars = OldWire.Replay Source.Pin.admission
strict-wire-unchanged : present (OldChars.verify Produced.dependent-caller-characters) ≡ false
strict-wire-unchanged = refl
inferred-kind-before-exact : R.Open.verify-in (R.Checked.context exact-checked) (R.Checked.context-valid exact-checked)
  0 (Caller.checking (record exact-query { inferred-kind-recipe = r-lam r-leaf r-leaf }))
  ≡ Ambient.rejected Ambient.inferred-kind-failed
inferred-kind-before-exact = refl
goal-kind-before-exact : R.Open.verify-in (R.Checked.context exact-checked) (R.Checked.context-valid exact-checked)
  0 (Caller.checking (with-call exact-query
    (record (Caller.Request.caller exact-query) { goal-recipe = r-lam r-leaf r-leaf })))
  ≡ Ambient.rejected Ambient.goal-kind-failed
goal-kind-before-exact = refl

missing-kind : present (R.verify 64 (with-call Dependent.query (record dependent-call { kind-recipes = r-leaf ∷ [] }))) ≡ false
missing-kind = refl
surplus-kind : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { kind-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] }))) ≡ false
surplus-kind = refl
missing-binding : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { bindings = ("A" , tm-type l0) ∷ [] }))) ≡ false
missing-binding = refl
surplus-binding : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { bindings = ("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ ("x" , tm-var 1) ∷ [] }))) ≡ false
surplus-binding = refl
escaped-declaration : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { bindings = ("A" , tm-var 0) ∷ ("x" , tm-var 0) ∷ [] }))) ≡ false
escaped-declaration = refl
universe-declaration : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { bindings = ("A" , tm-type l2) ∷ ("x" , tm-var 0) ∷ [] }))) ≡ false
universe-declaration = refl
missing-argument : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { arguments = tm-atom_type ∷ [] }))) ≡ false
missing-argument = refl
surplus-argument : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { arguments = tm-atom_type ∷ tm-atom_lit "payload" ∷ tm-atom_type ∷ [] }))) ≡ false
surplus-argument = refl
missing-argument-recipe : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { argument-recipes = r-leaf ∷ [] }))) ≡ false
missing-argument-recipe = refl
surplus-argument-recipe : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { argument-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] }))) ≡ false
surplus-argument-recipe = refl
reversed-arguments : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { arguments = tm-atom_lit "payload" ∷ tm-atom_type ∷ [] }))) ≡ false
reversed-arguments = refl
wrong-dependent-argument : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { arguments = tm-pi unrestricted tm-atom_type tm-atom_type ∷ tm-atom_lit "payload" ∷ []
    ; argument-recipes = r-pi r-leaf r-leaf ∷ r-leaf ∷ [] }))) ≡ false
wrong-dependent-argument = refl
escaped-argument : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { arguments = tm-atom_type ∷ tm-var 0 ∷ [] }))) ≡ false
escaped-argument = refl
unsupported-argument : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { arguments = tm-atom_type ∷ tm-hole "payload" ∷ [] }))) ≡ false
unsupported-argument = refl
escaped-subject : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { subject = tm-var 2 }))) ≡ false
escaped-subject = refl
nonkind-goal : present (R.verify 64 (with-call Dependent.query
  (record dependent-call { goal = tm-var 0 ; goal-recipe = r-leaf }))) ≡ false
nonkind-goal = refl

collision-query : Caller.Request
collision-query = query-of Produced.collision-caller-characters Produced.collision-kind-characters refl
collision-exact : Caller.Request
collision-exact = with-call collision-query
  (record (Caller.Request.caller collision-query) { goal = Produced.collision-inferred })
collision-frame : R.Checked collision-exact
collision-frame = pick (R.verify 0 collision-exact) refl
collision-size : R.Checked.size collision-frame ≡ Produced.collision-size
collision-size = refl
collision-inferred : R.Open.Checked.inferred (R.Checked.open-checked collision-frame) ≡ Produced.collision-inferred
collision-inferred = refl
collision-fresh : Fresh.environment 3 ≡ Produced.collision-environment
collision-fresh = refl
collision-left : Quote.term-result (Q.normalise-residual-with R.C.W.ind 64 3 Produced.collision-inferred
  Produced.collision-environment) ≡ just Produced.collision-open-left
collision-left = refl
collision-right : Quote.term-result (Q.normalise-residual-with R.C.W.ind 64 3
  (OldCaller.Request.goal (Caller.Request.caller collision-query)) Produced.collision-environment) ≡ just Produced.collision-open-right
collision-right = refl
collision-readback : Quote.term-result (Q.normalise-residual-with R.C.W.ind 64 0 Produced.collision-closed-subject [])
  ≡ just Produced.collision-closed-quoted
collision-readback = refl
-- Declaration, all three actuals and both kinds pass in the same frame.
collision-open-distinct : Compare.classify (Compare.compare-with R.C.W.ind 64 3 (Fresh.environment 3)
  Produced.collision-inferred (OldCaller.Request.goal (Caller.Request.caller collision-query))) ≡ Compare.distinct-forms
collision-open-distinct = refl
collision-actual-distinct : Produced.collision-actual ≡ false
collision-actual-distinct = refl
collision-rejected : present (R.verify 64 collision-query) ≡ false
collision-rejected = refl
collision-wire-rejected : present (Chars.verify Produced.collision-caller-characters Produced.collision-kind-characters) ≡ false
collision-wire-rejected = refl
closing-coincidence : substS (R.Checked.substitution collision-frame) Produced.collision-inferred
  ≡ substS (R.Checked.substitution collision-frame) (OldCaller.Request.goal (Caller.Request.caller collision-query))
closing-coincidence = refl
closed-instance-is-safe : R.C.Sound.SafeState Produced.collision-closed-subject Produced.collision-closed-goal
closed-instance-is-safe = R.Checked.trace-safe collision-frame ⇝*-refl
outside-prefix-is-not-identity : Meaning.environment-sub (Fresh.images 3) 3 ≢ tm-var 3
outside-prefix-is-not-identity ()

malformed-caller : present (Chars.verify ('(' ∷ []) Produced.dependent-kind-characters) ≡ false
malformed-caller = refl
malformed-kind : present (Chars.verify Produced.dependent-caller-characters ('(' ∷ [])) ≡ false
malformed-kind = refl
trailing-caller : present (Chars.verify (Produced.dependent-caller-characters ++ (';' ∷ []))
  Produced.dependent-kind-characters) ≡ false
trailing-caller = refl
trailing-kind : present (Chars.verify Produced.dependent-caller-characters
  (Produced.dependent-kind-characters ++ (';' ∷ []))) ≡ false
trailing-kind = refl
bad-kind-packet : List Char
bad-kind-packet = pick (RecipeWire.encode Bundle.table (r-lam r-leaf r-leaf)) refl
parsed-kind-is-not-admission : present (Chars.verify Produced.dependent-caller-characters bad-kind-packet) ≡ false
parsed-kind-is-not-admission = refl
missing-name : Wire.encode [] Dependent.query ≡ nothing
missing-name = refl
