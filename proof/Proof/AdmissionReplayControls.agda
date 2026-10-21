------------------------------------------------------------------------
-- Computed yes/no controls for syntax and complete raw payload replay.
-- In particular, metadata/projected success cannot hide a raw hole.
-- Syntax acceptance still does NOT imply native or executable typing.
------------------------------------------------------------------------
module Proof.AdmissionReplayControls where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (erased; unrestricted)
open import Core.Universe using (l0; l2)
open import Core.Signature using (Ctor)
import Core.Typing as Context
import Core.ExecutableSnapshot as Input
import Core.ExecutableReplay as Replay
import Fixtures.ExecutableSnapshot as Fixture
import Proof.ExecutableSnapshotExamples as E

module R = E.CompleteReplay.R

refutation : ∀ {A : Set} (checked : Dec A) → E.decision checked ≡ false → A → ⊥
refutation (yes proof) ()
refutation (no absent) negative = absent

module Hidden (body : Term) where
  source : Input.Input
  source = record Fixture.source
    { globals = record E.raw-held { body = just body } ∷ [] }
  metadata : Input.Accepted source
  metadata = E.witness (Input.check source) refl
  module Complete = Replay.Replay source metadata

  -- True for ANY raw body: projected visibility alone cannot inspect it.
  projected-still-supported : E.decision Complete.R.payloads? ≡ true
  projected-still-supported = refl
  checked-body : Complete.Payloads → Complete.R.Supported 0 body
  checked-body payloads = Complete.raw-body-supported payloads (here refl) refl

module Hole = Hidden (tm-hole "hidden")
hidden-hole-rejected : E.decision Hole.Complete.check ≡ false
hidden-hole-rejected = refl
hidden-hole-no-evidence : Hole.Complete.Payloads → ⊥
hidden-hole-no-evidence = refutation Hole.Complete.check refl

visible-hole : Input.Input
visible-hole = record Fixture.source
  { globals = record E.raw-answer { body = just (tm-hole "visible") } ∷ [] }
visible-hole-metadata : Input.Accepted visible-hole
visible-hole-metadata = E.witness (Input.check visible-hole) refl
module VisibleHole = Replay.Replay visible-hole visible-hole-metadata
visible-hole-projected-rejected : E.decision VisibleHole.R.payloads? ≡ false
visible-hole-projected-rejected = refl
visible-hole-rejected : E.decision VisibleHole.check ≡ false
visible-hole-rejected = refl

module Absurd = Hidden tm-absurd
hidden-absurd-rejected : E.decision Absurd.Complete.check ≡ false
hidden-absurd-rejected = refl
module Effect = Hidden (tm-effect_pure (tm-atom_lit "effect"))
hidden-effect-rejected : E.decision Effect.Complete.check ≡ false
hidden-effect-rejected = refl
module Escaped = Hidden (tm-var 0)
hidden-free-variable-rejected : E.decision Escaped.Complete.check ≡ false
hidden-free-variable-rejected = refl
module NestedHole = Hidden
  (tm-lam erased tm-atom_type (tm-let unrestricted tm-atom_type (tm-atom_lit "v") (tm-hole "nested")))
nested-erased-hole-rejected : E.decision NestedHole.Complete.check ≡ false
nested-erased-hole-rejected = refl
module SupportedHidden = Hidden
  (tm-let unrestricted tm-atom_type (tm-atom_lit "v") (tm-var 0))
supported-hidden-accepted : SupportedHidden.Complete.Payloads
supported-hidden-accepted = E.witness SupportedHidden.Complete.check refl

module IllTyped = Hidden (tm-app (tm-atom_lit "not-a-function") (tm-atom_lit "argument"))
ill-typed-syntax-still-represented : IllTyped.Complete.Payloads
ill-typed-syntax-still-represented = E.witness IllTyped.Complete.check refl

forward-dependent-telescope : E.decision
  (R.telescope? 0 (("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ [])) ≡ true
forward-dependent-telescope = refl
forward-reference-rejected : E.decision
  (R.telescope? 0 (("A" , tm-type l0) ∷ ("x" , tm-var 1) ∷ [])) ≡ false
forward-reference-rejected = refl
unsupported-annotation-rejected : E.decision
  (R.telescope? 0 (("A" , tm-type l0) ∷ ("x" , tm-float_lit) ∷ [])) ≡ false
unsupported-annotation-rejected = refl

bad-result : Ctor
bad-result = record E.pack { ctor-indices = tm-var 2 ∷ [] }
escaped-result-rejected : E.decision (R.constructor? E.packed bad-result) ≡ false
escaped-result-rejected = refl

missing-global-rejected : E.decision (R.supported? 0 (tm-global "missing")) ≡ false
missing-global-rejected = refl
foreign-family-rejected : E.decision (R.supported? 0 (tm-data "Foreign#Packed" [] [])) ≡ false
foreign-family-rejected = refl
bare-constructor-rejected : E.decision (R.supported? 0 (tm-ctor "Pack" [])) ≡ false
bare-constructor-rejected = refl
missing-branch-name-rejected : E.decision
  (R.branches? 0 (("Foreign#Pack" , 2 , tm-var 0) ∷ [])) ≡ false
missing-branch-name-rejected = refl
bad-branch-arity-rejected : E.decision
  (R.branches? 0 (("Boundary#Pack" , 1 , tm-var 0) ∷ [])) ≡ false
bad-branch-arity-rejected = refl
escaped-branch-rejected : E.decision
  (R.branches? 0 (("Boundary#Pack" , 2 , tm-var 2) ∷ [])) ≡ false
escaped-branch-rejected = refl
lambda-capture-supported : E.decision
  (R.branches? 0 (("Boundary#Pack" , 2 , tm-lam unrestricted tm-atom_type (tm-var 2)) ∷ [])) ≡ true
lambda-capture-supported = refl
escaped-lambda-capture-rejected : E.decision
  (R.branches? 0 (("Boundary#Pack" , 2 , tm-lam unrestricted tm-atom_type (tm-var 3)) ∷ [])) ≡ false
escaped-lambda-capture-rejected = refl
outer-caller-retained : E.decision
  (R.branches? 1 (("Boundary#Pack" , 2 , tm-var 2) ∷ [])) ≡ true
outer-caller-retained = refl

nested : Term
nested = tm-case
  (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "v" ∷ []))
  (tm-lam unrestricted (tm-type l0)
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1)))
  (("Boundary#Pack" , 2 ,
    tm-case
      (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "w" ∷ []))
      (tm-lam unrestricted (tm-type l0)
        (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1)))
      (("Boundary#Pack" , 2 , tm-var 3) ∷ [])) ∷ [])
nested-case-supported : E.decision (R.supported? 0 nested) ≡ true
nested-case-supported = refl
module Nested = Hidden nested
nested-hidden-accepted : Nested.Complete.Payloads
nested-hidden-accepted = E.witness Nested.Complete.check refl

open-variable-supported : E.decision (R.supported? 1 (tm-var 0)) ≡ true
open-variable-supported = refl
closed-free-variable-rejected : E.decision (R.supported? 0 (tm-var 0)) ≡ false
closed-free-variable-rejected = refl
caller-supported : E.decision
  (R.context? (Context.extend Context.⟨⟩ tm-atom_type)) ≡ true
caller-supported = refl
dependent-caller-supported : E.decision
  (R.context? (Context.extend (Context.extend Context.⟨⟩ (tm-type l0)) (tm-var 0))) ≡ true
dependent-caller-supported = refl
escaped-caller-type-rejected : E.decision
  (R.context? (Context.⟨⟩ Context.▷ tm-var 1)) ≡ false
escaped-caller-type-rejected = refl
hole-caller-type-rejected : E.decision
  (R.context? (Context.⟨⟩ Context.▷ tm-hole "caller")) ≡ false
hole-caller-type-rejected = refl

-- These deliberately succeed: the existing grammar is NOT the stronger
-- exporter arity/encoding policy, a coverage verifier or a kind checker.
incomplete-ctor-still-represented : E.decision
  (R.supported? 0 (tm-ctor "Boundary#Pack" [])) ≡ true
incomplete-ctor-still-represented = refl
ceiling-still-represented : E.decision (R.supported? 0 (tm-type l2)) ≡ true
ceiling-still-represented = refl
empty-case-still-represented : E.decision
  (R.supported? 0 (tm-case (tm-atom_lit "non-data") tm-atom_type [])) ≡ true
empty-case-still-represented = refl

float-payload-rejected : E.decision (R.supported? 0 tm-float_lit) ≡ false
float-payload-rejected = refl
int-type-rejected : E.decision (R.supported? 0 tm-int_type) ≡ false
int-type-rejected = refl
int-literal-rejected : E.decision (R.supported? 0 (tm-int_lit (pos 0))) ≡ false
int-literal-rejected = refl
nat-literal-rejected : E.decision (R.supported? 0 (tm-nat_lit 0)) ≡ false
nat-literal-rejected = refl
bounded-literal-rejected : E.decision (R.supported? 0 (tm-bounded_lit 0)) ≡ false
bounded-literal-rejected = refl
effect-type-rejected : E.decision (R.supported? 0 (tm-effect_type tm-atom_type)) ≡ false
effect-type-rejected = refl
effect-bind-rejected : E.decision
  (R.supported? 0 (tm-effect_bind (tm-atom_lit "e") (tm-atom_lit "k"))) ≡ false
effect-bind-rejected = refl
