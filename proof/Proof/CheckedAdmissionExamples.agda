{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- No caller metadata, payload, conversion or validity proof is supplied
-- to the verifier. Every result is indexed by actual source/characters.
------------------------------------------------------------------------
module Proof.CheckedAdmissionExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (yes; no)
open import Core.Syntax
open import Core.Universe using (l2)
open import Core.Reduction using (Signature; _⇝_; _⇝*_; δ; ι; ⇝*-step; ⇝*-refl)
open import Core.NativeRecipe using (packet; r-leaf)
import Core.CheckedAdmission as P
import Core.ExecutableSnapshot as I
import Core.ExecutableReplay as Payloads
import Core.Wire as W
import Core.WireCertificate as Codec
import Fixtures.ExecutableSnapshot as Source
import Fixtures.ExecutableCertificate as Produced
import Proof.WireCertificateExamples as Wire
import Proof.ProducedCertificateExamples as Artifact
import Proof.ExecutableSnapshotExamples as Snapshot
open P using (present)

pick : ∀ {A : Set} (result : Maybe A) → present result ≡ true → A
pick nothing ()
pick (just value) successful = value
pick-equation : ∀ {A : Set} (result : Maybe A) (successful : present result ≡ true)
  → result ≡ just (pick result successful)
pick-equation nothing ()
pick-equation (just value) successful = refl

-- Abstract only the extracted proof, not verification or success. The
-- accompanying equation retains the exact verifier-result connection.
abstract
  obtain : ∀ {A : Set} (result : Maybe A) → present result ≡ true → A
  obtain = pick
  obtain-result : ∀ {A : Set} (result : Maybe A) (successful : present result ≡ true)
    → result ≡ just (obtain result successful)
  obtain-result nothing ()
  obtain-result (just value) successful = refl

accepted : present (P.verify Source.source Produced.table Produced.characters) ≡ true
accepted = trans (P.verify-decoded Source.source Produced.table Produced.characters
  Wire.payload Artifact.produced-decoding) refl
checked : P.Checked Source.source Produced.table Produced.characters
checked = obtain (P.verify Source.source Produced.table Produced.characters) accepted
exact-result : P.verify Source.source Produced.table Produced.characters ≡ just checked
exact-result = obtain-result (P.verify Source.source Produced.table Produced.characters) accepted
module C = P.Checked checked
module B = P.Bodies checked

unpack : B.Body "Boundary#unpack"
unpack = pick (B.admit "Boundary#unpack") refl
selected-program : B.Body.term unpack ≡
  pick (I.GlobalInput.body Snapshot.raw-unpack) refl
selected-program = refl
original-goal : B.Body.goal unpack ≡ tm-atom_type
original-goal = refl
unpack-safe : C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
unpack-safe = B.Body.trace-safe unpack (⇝*-step (ι refl refl) ⇝*-refl)
fuel-result : C.Sound.FuelResult (B.Body.term unpack) tm-atom_type
fuel-result = B.Body.run unpack 2
tree : C.Sound.EvalTree (B.Body.term unpack) tm-atom_type
tree = B.Body.tree unpack
budgets-agree : ∀ fuel → B.Body.run unpack fuel ≡ C.Sound.truncate fuel tree
budgets-agree = B.Body.budgets-agree unpack
held : B.Body "Boundary#held"
held = pick (B.admit "Boundary#held") refl
hidden-body-retained : B.Body.term held ≡ tm-atom_lit "hidden"
hidden-body-retained = refl
hidden-body-not-delta : Signature.body C.W.sig "Boundary#held" ≡ nothing
hidden-body-not-delta = refl
unknown-name-rejected : present (B.admit "Boundary#missing") ≡ false
unknown-name-rejected = refl
bare-alias-rejected : present (B.admit "unpack") ≡ false
bare-alias-rejected = refl
malformed-characters : present (P.verify Source.source Produced.table ('(' ∷ [])) ≡ false
malformed-characters = refl

module Attempt (source : I.Input) (recipes : Codec.Envelope)
  (encoded : present (Codec.to-node Produced.table recipes) ≡ true) where
  node : W.Node
  node = pick (Codec.to-node Produced.table recipes) encoded
  written : Codec.to-node Produced.table recipes ≡ just node
  written = pick-equation (Codec.to-node Produced.table recipes) encoded
  characters : List Char
  characters = W.encode node
  status : ∀ wanted → P.data-status source recipes ≡ wanted
    → present (P.verify source Produced.table characters) ≡ wanted
  status wanted successful = trans (P.verify-encoding source Produced.table recipes node written) successful

empty-recipes : Codec.Envelope
empty-recipes = Codec.envelope [] []
module Duplicate = Attempt Snapshot.duplicate-families Wire.payload refl
duplicates-rejected : present (P.verify Snapshot.duplicate-families Produced.table Duplicate.characters) ≡ false
duplicates-rejected = Duplicate.status false refl
module Erased = Attempt Snapshot.erased-fields Wire.payload refl
erased-layout-rejected : present (P.verify Snapshot.erased-fields Produced.table Erased.characters) ≡ false
erased-layout-rejected = Erased.status false refl
module Missing = Attempt Source.source empty-recipes refl
missing-certificate-rejected : present (P.verify Source.source Produced.table Missing.characters) ≡ false
missing-certificate-rejected = Missing.status false refl

bad-hidden : I.Input
bad-hidden = record Source.source
  { globals = record Snapshot.raw-held { body = just (tm-hole "hidden") } ∷ [] }
hidden-metadata-passes : Snapshot.decision (I.check bad-hidden) ≡ true
hidden-metadata-passes = refl
hidden-metadata : I.Accepted bad-hidden
hidden-metadata = Snapshot.witness (I.check bad-hidden) hidden-metadata-passes
hidden-payload-fails : Snapshot.decision (Payloads.Replay.check bad-hidden hidden-metadata) ≡ false
hidden-payload-fails = refl
module Hidden = Attempt bad-hidden empty-recipes refl
unsupported-hidden-payload-rejected : present (P.verify bad-hidden Produced.table Hidden.characters) ≡ false
unsupported-hidden-payload-rejected = Hidden.status false refl

scalar-recipes : Codec.Envelope
scalar-recipes = Codec.envelope [] (packet r-leaf (just r-leaf) ∷ [])
representation-status : I.Input → Bool
representation-status source with I.check source
... | no rejected = false
... | yes metadata = Snapshot.decision (Payloads.Replay.check source metadata)
bad-kind : I.Input
bad-kind = I.input []
  (I.global-input "Bad#kind" (tm-type l2) (just (tm-atom_lit "payload"))
    nothing nothing false false ∷ []) []
module BadKind = Attempt bad-kind scalar-recipes refl
ill-kinded-representation-passes : representation-status bad-kind ≡ true
ill-kinded-representation-passes = refl
ill-kinded-rejected : present (P.verify bad-kind Produced.table BadKind.characters) ≡ false
ill-kinded-rejected = BadKind.status false refl
bad-body : I.Input
bad-body = I.input []
  (I.global-input "Bad#body" tm-float_type (just (tm-atom_lit "payload"))
    nothing nothing false false ∷ []) []
module BadBody = Attempt bad-body scalar-recipes refl
ill-typed-representation-passes : representation-status bad-body ≡ true
ill-typed-representation-passes = refl
ill-typed-rejected : present (P.verify bad-body Produced.table BadBody.characters) ≡ false
ill-typed-rejected = BadBody.status false refl

no-body : I.Input
no-body = I.input []
  (I.global-input "Empty#body" tm-atom_type nothing nothing nothing false false ∷ []) []
module NoBody = Attempt no-body (Codec.envelope [] (packet r-leaf nothing ∷ [])) refl
no-body-accepted : present (P.verify no-body Produced.table NoBody.characters) ≡ true
no-body-accepted = NoBody.status true refl
no-body-checked : P.Checked no-body Produced.table NoBody.characters
no-body-checked = obtain (P.verify no-body Produced.table NoBody.characters) no-body-accepted
module Absent = P.Bodies no-body-checked
absent-body-not-admitted : present (Absent.admit "Empty#body") ≡ false
absent-body-not-admitted = refl

-- Certification claims and final bodies do NOT imply semantic termination.
recursive : I.Input
recursive = I.input []
  (I.global-input "Loop#loop" tm-atom_type (just (tm-global "Loop#loop"))
    nothing nothing true true ∷ []) []
module Recursive = Attempt recursive scalar-recipes refl
recursive-accepted : present (P.verify recursive Produced.table Recursive.characters) ≡ true
recursive-accepted = Recursive.status true refl
recursive-checked : P.Checked recursive Produced.table Recursive.characters
recursive-checked = obtain (P.verify recursive Produced.table Recursive.characters) recursive-accepted
module Loop = P.Checked recursive-checked
module LoopBodies = P.Bodies recursive-checked
loop : LoopBodies.Body "Loop#loop"
loop = pick (LoopBodies.admit "Loop#loop") refl
loop-step : _⇝_ Loop.W.sig (LoopBodies.Body.term loop) (LoopBodies.Body.term loop)
loop-step = δ refl
loop-safe : Loop.Sound.SafeState (tm-global "Loop#loop") tm-atom_type
loop-safe = LoopBodies.Body.trace-safe loop (⇝*-step loop-step ⇝*-refl)
