{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Explicit dependent caller data, not an asserted semantic environment.
-- The same typed substitution closes both open subject and expected goal.
------------------------------------------------------------------------
module Proof.CallerAdmissionExamples where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l2)
open import Core.NativeRecipe
import Core.CallerAdmission as Caller
import Core.WireCaller as Wire
import Core.WireConversion as Tags
import Core.Wire as W
import Proof.WireSnapshotExamples as Source
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as E
import Fixtures.ExecutableBundle as Bundle
import Fixtures.ExecutableCaller as Produced
open import Proof.CheckedAdmissionExamples using (pick; pick-equation; obtain; obtain-result)
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (ζ; ι; ⇝*-step; ⇝*-refl)
open Caller using (Request; request)
module R = Caller.Replay Source.Pin.admission
module Chars = Wire.Replay Source.Pin.admission

dependent : Request
dependent = request
  (("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ []) (r-leaf ∷ r-leaf ∷ [])
  (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) (r-leaf ∷ r-leaf ∷ [])
  (tm-var 0) (tm-var 1) r-leaf r-leaf
encoded : Wire.encode Bundle.table dependent ≡ just Produced.characters
encoded = refl
decoded : Wire.decode Bundle.table Produced.characters ≡ just dependent
decoded = Wire.roundtrip Bundle.table dependent Produced.characters encoded
accepted : present (Chars.verify Produced.characters) ≡ true
accepted = trans (Chars.verify-decoded Produced.characters dependent decoded) refl
wire-checked : Chars.Checked Produced.characters
wire-checked = obtain (Chars.verify Produced.characters) accepted
exact-wire-result : Chars.verify Produced.characters ≡ just wire-checked
exact-wire-result = obtain-result (Chars.verify Produced.characters) accepted
-- The explicit decoder equation also pins this request's eight fields.
dependent-checked : R.Checked dependent
dependent-checked = Chars.pin wire-checked dependent decoded
closed-variable : R.Checked.closed-subject dependent-checked ≡ tm-atom_lit "payload"
closed-variable = refl
closed-goal : R.Checked.closed-goal dependent-checked ≡ tm-atom_type
closed-goal = refl
last-argument-at-zero : R.Checked.substitution dependent-checked 0 ≡ tm-atom_lit "payload"
last-argument-at-zero = refl
first-argument-at-one : R.Checked.substitution dependent-checked 1 ≡ tm-atom_type
first-argument-at-one = refl
identity-safe : R.C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
identity-safe = R.Checked.trace-safe dependent-checked ⇝*-refl

constructor-query : Request
constructor-query = record dependent
  { subject = tm-ctor "Boundary#Pack" (tm-var 1 ∷ tm-var 0 ∷ [])
  ; goal = tm-data "Boundary#Packed" [] (tm-var 1 ∷ [])
  ; subject-recipe = r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])
  ; goal-recipe = r-data [] (r-leaf ∷ []) }
constructor-checked : R.Checked constructor-query
constructor-checked = pick (R.verify constructor-query) refl
dependent-result-index : R.Checked.closed-goal constructor-checked ≡ E.goal
dependent-result-index = refl
constructor-safe : R.C.Sound.SafeState E.value E.goal
constructor-safe = R.Checked.trace-safe constructor-checked ⇝*-refl

let-query : Request
let-query = record dependent
  { subject = tm-let unrestricted (tm-var 1) (tm-var 0) (tm-var 0)
  ; subject-recipe = r-let r-leaf r-leaf r-leaf }
let-checked : R.Checked let-query
let-checked = pick (R.verify let-query) refl
let-closed : R.Checked.closed-subject let-checked ≡
  tm-let unrestricted tm-atom_type (tm-atom_lit "payload") (tm-var 0)
let-closed = refl
zeta-safe : R.C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
zeta-safe = R.Checked.trace-safe let-checked (⇝*-step ζ ⇝*-refl)
fuel : R.C.Sound.FuelResult (R.Checked.closed-subject let-checked) tm-atom_type
fuel = R.Checked.run let-checked 2
tree : R.C.Sound.EvalTree (R.Checked.closed-subject let-checked) tm-atom_type
tree = R.Checked.tree let-checked
budgets-agree : ∀ budget → R.Checked.run let-checked budget ≡ R.C.Sound.truncate budget tree
budgets-agree = R.Checked.budgets-agree let-checked

missing-kind : present (R.verify (record dependent { kind-recipes = r-leaf ∷ [] })) ≡ false
missing-kind = refl
missing-binding : present
  (R.verify (record dependent { bindings = ("A" , tm-type l0) ∷ [] })) ≡ false
missing-binding = refl
surplus-binding : present
  (R.verify (record dependent
    { bindings = ("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ ("x" , tm-var 1) ∷ [] })) ≡ false
surplus-binding = refl
surplus-kind : present
  (R.verify (record dependent { kind-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] })) ≡ false
surplus-kind = refl
missing-argument : present (R.verify (record dependent { arguments = tm-atom_type ∷ [] })) ≡ false
missing-argument = refl
surplus-argument : present
  (R.verify (record dependent { arguments = tm-atom_type ∷ tm-atom_lit "payload" ∷ tm-atom_type ∷ [] })) ≡ false
surplus-argument = refl
missing-argument-recipe : present
  (R.verify (record dependent { argument-recipes = r-leaf ∷ [] })) ≡ false
missing-argument-recipe = refl
surplus-argument-recipe : present
  (R.verify (record dependent { argument-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] })) ≡ false
surplus-argument-recipe = refl
reversed-arguments : present
  (R.verify (record dependent { arguments = tm-atom_lit "payload" ∷ tm-atom_type ∷ [] })) ≡ false
reversed-arguments = refl
wrong-dependent-argument : present
  (R.verify (record dependent { arguments = tm-float_type ∷ tm-atom_lit "payload" ∷ [] })) ≡ false
wrong-dependent-argument = refl
escaped-argument : present
  (R.verify (record dependent { arguments = tm-atom_type ∷ tm-var 0 ∷ [] })) ≡ false
escaped-argument = refl
unsupported-argument : present
  (R.verify (record dependent { arguments = tm-atom_type ∷ tm-hole "payload" ∷ [] })) ≡ false
unsupported-argument = refl
escaped-declaration : present
  (R.verify (record dependent { bindings = ("A" , tm-var 0) ∷ ("x" , tm-var 0) ∷ [] })) ≡ false
escaped-declaration = refl
ill-kinded-declaration : present
  (R.verify (record dependent { bindings = ("A" , tm-type l2) ∷ ("x" , tm-var 0) ∷ [] })) ≡ false
ill-kinded-declaration = refl
wrong-goal : present (R.verify (record dependent { goal = tm-float_type })) ≡ false
wrong-goal = refl
non-kind-goal : present (R.verify (record dependent { goal = tm-var 0 })) ≡ false
non-kind-goal = refl
escaped-subject : present (R.verify (record dependent { subject = tm-var 2 })) ≡ false
escaped-subject = refl

case-query : Request
case-query = record dependent
  { subject = E.program ; goal = tm-atom_type
  ; subject-recipe = r-convert tm-atom_type Recipes.unpack-conversion Recipes.unpack-case-recipe }
-- The declaration-derived context witness now reaches case replay.
nonempty-case-now-checked : present (R.verify case-query) ≡ true
nonempty-case-now-checked = refl
empty-case-query : Request
empty-case-query = record case-query
  { bindings = [] ; kind-recipes = [] ; arguments = [] ; argument-recipes = [] }
empty-case-checked : R.Checked empty-case-query
empty-case-checked = pick (R.verify empty-case-query) refl
case-safe : R.C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
case-safe = R.Checked.trace-safe empty-case-checked (⇝*-step (ι refl refl) ⇝*-refl)
wrong-tag : Wire.from-node Bundle.table (Tags.tagged 18 []) ≡ nothing
wrong-tag = refl
malformed-caller : present (Chars.verify ('(' ∷ [])) ≡ false
malformed-caller = refl

module Attempt (query : Request) (written : present (Wire.to-node Bundle.table query) ≡ true) where
  node : W.Node
  node = pick (Wire.to-node Bundle.table query) written
  encoded-node : Wire.to-node Bundle.table query ≡ just node
  encoded-node = pick-equation (Wire.to-node Bundle.table query) written
  status : ∀ expected → present (R.verify query) ≡ expected
    → present (Chars.verify (W.encode node)) ≡ expected
  status expected result = trans
    (Chars.verify-decoded (W.encode node) query (Wire.character-fidelity Bundle.table query node encoded-node)) result

module Reversed = Attempt
  (record dependent { arguments = tm-atom_lit "payload" ∷ tm-atom_type ∷ [] }) refl
reversed-wire-rejected : present (Chars.verify (W.encode Reversed.node)) ≡ false
reversed-wire-rejected = Reversed.status false reversed-arguments
module WrongGoal = Attempt (record dependent { goal = tm-float_type }) refl
wrong-goal-wire-rejected : present (Chars.verify (W.encode WrongGoal.node)) ≡ false
wrong-goal-wire-rejected = WrongGoal.status false wrong-goal
missing-query-name : Wire.to-node [] dependent ≡ nothing
missing-query-name = refl
surplus-root-child : Wire.from-node Bundle.table
  (Tags.tagged 19 (W.n-list [] ∷ W.n-list [] ∷ [])) ≡ nothing
surplus-root-child = refl
trailing-character : Wire.decode Bundle.table (Produced.characters ++ (';' ∷ [])) ≡ nothing
trailing-character = refl
