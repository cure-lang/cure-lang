{-# OPTIONS --guardedness #-}
module Proof.ArgumentCallerExamples where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l2)
open import Core.NativeRecipe using (Recipe; r-leaf; r-app; r-lam)
open import Core.CheckedAdmission using (present)
open import Core.Reduction using (⇝*-refl)
import Core.ArgumentAdmission as Argument
import Core.ArgumentCallerAdmission as Caller
import Core.CallerAdmission as Exact
import Core.ResidualCallerAdmission as Residual
import Core.WireArgumentCaller as Wire
import Core.WireCaller as OldWire
import Core.WireConversion as Tags
import Core.Wire as W
import Proof.WireSnapshotExamples as Source
import Proof.CallerAdmissionExamples as Existing
import Fixtures.ExecutableBundle as Bundle
open import Proof.CheckedAdmissionExamples using (pick; pick-equation)

module R = Caller.Replay Source.Pin.admission
module Packet = Wire.Replay Source.Pin.admission 4 Argument.residual-guided

identity-type : Term → Term
identity-type t = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) t

beta-recipe : Recipe
beta-recipe = r-app (r-lam r-leaf r-leaf) r-leaf

-- The second type mentions A; substituting the preceding actual changes
-- this OPEN declaration into (λ B → B) Atom, not into Atom itself.
call : Exact.Request
call = Exact.request
  (("A" , tm-type l0) ∷ ("x" , identity-type (tm-var 0)) ∷ [])
  (r-leaf ∷ beta-recipe ∷ [])
  (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
  (r-leaf ∷ r-leaf ∷ [])
  (tm-var 0) (identity-type (tm-var 1)) r-leaf beta-recipe

query : Caller.Request
query = Caller.request (Residual.request call beta-recipe) (r-leaf ∷ r-leaf ∷ [])

nonexact : identity-type tm-atom_type ≢ tm-atom_type
nonexact ()

accepted : present (R.verify 4 Argument.residual-guided query) ≡ true
accepted = refl
exact-driver-refuses : present (Existing.R.verify call) ≡ false
exact-driver-refuses = refl
old-residual-driver-refuses : present (R.Old.verify 4 (Caller.Request.caller query)) ≡ false
old-residual-driver-refuses = refl
exhausted : present (R.verify 3 Argument.residual-guided query) ≡ false
exhausted = refl
exact-only-refuses : present (R.verify 4 Argument.exact-only query) ≡ false
exact-only-refuses = refl

-- Construct a packet with the real encoder, then independently decode
-- and replay it. The general codec roundtrip is not a fixture assumption.
node : W.Node
node = pick (Wire.to-node Bundle.table query) refl
written : Wire.to-node Bundle.table query ≡ just node
written = pick-equation (Wire.to-node Bundle.table query) refl
characters : List Char
characters = W.encode node
decoded : Wire.decode Bundle.table characters ≡ just query
decoded = Wire.character-fidelity Bundle.table query node written
wire-accepted : present (Packet.verify characters) ≡ true
wire-accepted = trans (Packet.verify-decoded characters query decoded) accepted
packet : Packet.Checked characters
packet = pick (Packet.verify characters) wire-accepted
checked : R.Checked query
checked = Packet.pin packet query decoded
module Closed = R.Old.Checked checked
closed-subject : Closed.closed-subject ≡ tm-atom_lit "payload"
closed-subject = refl
original-closed-goal : Closed.closed-goal ≡ identity-type tm-atom_type
original-closed-goal = refl
last-actual-at-zero : Closed.substitution 0 ≡ tm-atom_lit "payload"
last-actual-at-zero = refl
first-actual-at-one : Closed.substitution 1 ≡ tm-atom_type
first-actual-at-one = refl
safe-at-original-goal : R.C.Sound.SafeState (tm-atom_lit "payload") (identity-type tm-atom_type)
safe-at-original-goal = Closed.trace-safe ⇝*-refl
budgets-agree : ∀ fuel → Closed.run fuel ≡ R.C.Sound.truncate fuel Closed.tree
budgets-agree = Closed.budgets-agree

exact-query : Caller.Request
exact-query = Caller.request (Residual.request Existing.dependent r-leaf) (r-leaf ∷ r-leaf ∷ [])
zero-budget-exact : present (R.verify 0 Argument.exact-only exact-query) ≡ true
zero-budget-exact = refl

-- Both stages can normalize in one request. Conversely, disabling
-- argument normalization does not disable fresh open-subject comparison.
both-normalized : Caller.Request
both-normalized = record query
  { caller = Residual.request (record call { goal = tm-var 1 ; goal-recipe = r-leaf }) beta-recipe }
both-normalized-accepted : present (R.verify 4 Argument.residual-guided both-normalized) ≡ true
both-normalized-accepted = refl
open-only : Caller.Request
open-only = record exact-query
  { caller = Residual.request
      (record Existing.dependent { goal = identity-type (tm-var 1) ; goal-recipe = beta-recipe }) r-leaf }
open-comparison-independent : present (R.verify 4 Argument.exact-only open-only) ≡ true
open-comparison-independent = refl
open-exhaustion : present (R.verify 3 Argument.exact-only open-only) ≡ false
open-exhaustion = refl

replace : Exact.Request → Caller.Request
replace c = record query { caller = Residual.request c beta-recipe }

missing-kind : present (R.verify 4 Argument.residual-guided
  (record query { argument-kind-recipes = r-leaf ∷ [] })) ≡ false
missing-kind = refl
surplus-kind : present (R.verify 4 Argument.residual-guided
  (record query { argument-kind-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] })) ≡ false
surplus-kind = refl
bad-inferred-kind : present (R.verify 0 Argument.exact-only
  (record exact-query { argument-kind-recipes = r-lam r-leaf r-leaf ∷ r-leaf ∷ [] })) ≡ false
bad-inferred-kind = refl
bad-expected-kind : present (R.verify 4 Argument.residual-guided
  (replace (record call { bindings = ("A" , tm-type l2) ∷ ("x" , tm-var 0) ∷ [] }))) ≡ false
bad-expected-kind = refl
missing-recipe : present (R.verify 4 Argument.residual-guided
  (replace (record call { argument-recipes = r-leaf ∷ [] }))) ≡ false
missing-recipe = refl
surplus-recipe : present (R.verify 4 Argument.residual-guided
  (replace (record call { argument-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] }))) ≡ false
surplus-recipe = refl
malformed-recipe : present (R.verify 4 Argument.residual-guided
  (replace (record call { argument-recipes = r-leaf ∷ beta-recipe ∷ [] }))) ≡ false
malformed-recipe = refl
reversed : present (R.verify 4 Argument.residual-guided
  (replace (record call { arguments = tm-atom_lit "payload" ∷ tm-atom_type ∷ [] }))) ≡ false
reversed = refl
wrong-dependent : present (R.verify 4 Argument.residual-guided
  (replace (record call { arguments = tm-float_type ∷ tm-atom_lit "payload" ∷ [] }))) ≡ false
wrong-dependent = refl
escaped : present (R.verify 4 Argument.residual-guided
  (replace (record call { arguments = tm-atom_type ∷ tm-var 0 ∷ [] }))) ≡ false
escaped = refl
missing-actual : present (R.verify 4 Argument.residual-guided
  (replace (record call { arguments = tm-atom_type ∷ [] }))) ≡ false
missing-actual = refl
surplus-actual : present (R.verify 4 Argument.residual-guided
  (replace (record call { arguments = tm-atom_type ∷ tm-atom_lit "payload" ∷ tm-atom_type ∷ [] }))) ≡ false
surplus-actual = refl
unsupported : present (R.verify 4 Argument.residual-guided
  (replace (record call { arguments = tm-atom_type ∷ tm-hole "payload" ∷ [] }))) ≡ false
unsupported = refl

-- Equal actuals must not turn two abstract type slots into open equality.
collision-call : Exact.Request
collision-call = Exact.request
  (("A" , tm-type l0) ∷ ("A" , tm-type l0) ∷ ("x" , tm-var 1) ∷ [])
  (r-leaf ∷ r-leaf ∷ r-leaf ∷ [])
  (tm-atom_type ∷ tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
  (r-leaf ∷ r-leaf ∷ r-leaf ∷ [])
  (tm-var 0) (tm-var 1) r-leaf r-leaf
collision : Caller.Request
collision = Caller.request (Residual.request collision-call r-leaf) (r-leaf ∷ r-leaf ∷ r-leaf ∷ [])
collision-rejected : present (R.verify 4 Argument.residual-guided collision) ≡ false
collision-rejected = refl
collision-exact : Caller.Request
collision-exact = record collision
  { caller = Residual.request (record collision-call { goal = tm-var 2 }) r-leaf }
collision-frame : R.Checked collision-exact
collision-frame = pick (R.verify 0 Argument.exact-only collision-exact) refl
closing-coincidence :
  substS (R.Old.Checked.substitution collision-frame) (tm-var 1)
    ≡ substS (R.Old.Checked.substitution collision-frame) (tm-var 2)
closing-coincidence = refl

module Attempt (q : Caller.Request) (encodable : present (Wire.to-node Bundle.table q) ≡ true) where
  encoded-node : W.Node
  encoded-node = pick (Wire.to-node Bundle.table q) encodable
  status : ∀ result → present (R.verify 4 Argument.residual-guided q) ≡ result
    → present (Packet.verify (W.encode encoded-node)) ≡ result
  status result verified = trans
    (Packet.verify-decoded (W.encode encoded-node) q
      (Wire.character-fidelity Bundle.table q encoded-node
        (pick-equation (Wire.to-node Bundle.table q) encodable))) verified

module CollisionPacket = Attempt collision refl
collision-wire-rejected : present (Packet.verify (W.encode CollisionPacket.encoded-node)) ≡ false
collision-wire-rejected = CollisionPacket.status false collision-rejected
module BadKindPacket = Attempt (record query { argument-kind-recipes = r-lam r-leaf r-leaf ∷ r-leaf ∷ [] }) refl
parsed-kind-is-not-admission : present (Packet.verify (W.encode BadKindPacket.encoded-node)) ≡ false
parsed-kind-is-not-admission = BadKindPacket.status false refl
module SurplusPacket = Attempt (record query { argument-kind-recipes = r-leaf ∷ r-leaf ∷ r-leaf ∷ [] }) refl
surplus-wire-rejected : present (Packet.verify (W.encode SurplusPacket.encoded-node)) ≡ false
surplus-wire-rejected = SurplusPacket.status false surplus-kind

trailing-character : Wire.decode Bundle.table (characters ++ (';' ∷ [])) ≡ nothing
trailing-character = refl
wrong-tag : Wire.from-node Bundle.table (Tags.tagged 20 []) ≡ nothing
wrong-tag = refl
surplus-root : Wire.from-node Bundle.table (Tags.tagged 21 (node ∷ node ∷ [])) ≡ nothing
surplus-root = refl
old-decoder-refuses : OldWire.decode Bundle.table characters ≡ nothing
old-decoder-refuses = refl
malformed-packet : present (Packet.verify ('(' ∷ [])) ≡ false
malformed-packet = refl
