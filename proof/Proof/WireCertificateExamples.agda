{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- The COMPLETE exported fixture's recipe certificate goes through
-- characters -> data -> native replay -> validity/admission -> safety.
-- No native family/global evidence is substituted for a decoded field.
------------------------------------------------------------------------
module Proof.WireCertificateExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
open import Core.Syntax
open import Core.Typing using (⟨⟩)
open import Core.Universe using (l0)
open import Core.Reduction using (⇝*-step; ⇝*-refl; ι)
open import Core.NativeRecipe
import Core.Wire as W
import Core.WireRecipe as R
import Core.WireConversion as C
import Core.WireCertificate as Codec
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as E
import Proof.NativeCertificateSafety as Existing
import Proof.ExecutableSnapshotExamples as Input
import Proof.DependentSoundness as Safety
import Fixtures.ExecutableSnapshot as Fixture
open Recipes using (present; require; scalar-packet; packed-packet; unpack-packet; fixture-recipes)
open W using (Node; n-atom; n-list)

table : List Name
table = "" ∷ "Boundary#Packed" ∷ "Boundary#Pack" ∷ "Boundary#Alternate" ∷ "payload" ∷ []
module Replay = Codec.Replay Fixture.source Input.accepted Input.replayed E.conv
  (λ {t} {u} → Input.ConversionModel.reduce-converts {t = t} {u = u})

require-equation : ∀ {A : Set} (result : Maybe A) (accepted : present result ≡ true)
  → result ≡ just (require result accepted)
require-equation nothing ()
require-equation (just value) accepted = refl

-- Avoid repeatedly normalizing a large character scanner in every
-- semantic control. Each instance must still establish encoder success;
-- generic character fidelity transports the ACTUAL replay, not a proof.
module Transport (value : Codec.Envelope) (encoded : present (Codec.to-node table value) ≡ true) where
  node : Node
  node = require (Codec.to-node table value) encoded
  written : Codec.to-node table value ≡ just node
  written = require-equation (Codec.to-node table value) encoded
  characters : List Char
  characters = W.encode node
  decoded : Codec.decode table characters ≡ just value
  decoded = Codec.character-fidelity table value node written
  agrees : Replay.checked table characters ≡
    Replay.G.certificate (Codec.Envelope.families value) (Codec.Envelope.packets value)
  agrees = Replay.checked-fidelity table value node written
  status : (expected : Bool)
    → present (Replay.G.certificate (Codec.Envelope.families value) (Codec.Envelope.packets value)) ≡ expected
    → present (Replay.checked table characters) ≡ expected
  status expected successful = trans (cong present agrees) successful
  abstract
    evidence : present (Replay.checked table characters) ≡ true → Replay.G.C.Evidence
    evidence successful = require
      (Replay.G.certificate (Codec.Envelope.families value) (Codec.Envelope.packets value))
      (subst (λ result → present result ≡ true) agrees successful)
    evidence-result : (successful : present (Replay.checked table characters) ≡ true)
      → Replay.checked table characters ≡ just (evidence successful)
    evidence-result successful = trans agrees
      (require-equation
        (Replay.G.certificate (Codec.Envelope.families value) (Codec.Envelope.packets value))
        (subst (λ result → present result ≡ true) agrees successful))

packets : List Packet
packets = scalar-packet ∷ scalar-packet ∷ packed-packet ∷ unpack-packet ∷ []
payload : Codec.Envelope
payload = Codec.envelope fixture-recipes packets
module Complete = Transport payload refl
character-encoding : Codec.encode table payload ≡ just Complete.characters
character-encoding = refl
character-roundtrip : Codec.decode table Complete.characters ≡ just payload
character-roundtrip = Codec.roundtrip table payload Complete.characters character-encoding
accepted : present (Replay.checked table Complete.characters) ≡ true
accepted = Complete.status true refl
certificate : Replay.G.C.Evidence
certificate = Complete.evidence accepted
certificate-from-characters : Replay.checked table Complete.characters ≡ just certificate
certificate-from-characters = Complete.evidence-result accepted
valid : E.N.SignatureValid
valid = Replay.G.C.validity certificate
admitted : E.N.Admitted ⟨⟩ E.program tm-atom_type
admitted = Replay.G.C.admitted certificate {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl
eligible : Replay.G.C.A.Eligible ⟨⟩ E.program tm-atom_type
eligible = Replay.G.C.eligible certificate {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl
specification : Safety.Specification E.ind E.sig E.conv
specification = record Existing.specification
  { signature-valid = valid
  ; reduction-converts = λ {t} {u} → Input.ConversionModel.reduce-converts {t = t} {u = u}
  ; global-bodies-final = λ {name} → Input.visible-bodies-final {name} }
module Sound = Safety.Sound E.ind E.sig E.conv specification
safe : Sound.SafeState (tm-atom_lit "payload") tm-atom_type
safe = Sound.trace-safe (Replay.G.C.A.Eligible.checked eligible)
  (Replay.G.C.A.Eligible.source-final eligible) (⇝*-step (ι refl refl) ⇝*-refl)

-- Container fidelity preserves ABSENT versus PRESENT body recipes.
leaf : Node
leaf = C.tagged 0 []
absent-body : Codec.from-packet [] (C.tagged 11 (leaf ∷ n-list [] ∷ []))
  ≡ just (packet r-leaf nothing)
absent-body = refl
present-body : Codec.from-packet [] (C.tagged 11 (leaf ∷ n-list (leaf ∷ []) ∷ []))
  ≡ just scalar-packet
present-body = refl
unknown-tag : Codec.from-node table (C.tagged 15 []) ≡ nothing
unknown-tag = refl
wrong-envelope-shape : Codec.from-node table (C.tagged 14 (n-atom 0 ∷ n-list [] ∷ [])) ≡ nothing
wrong-envelope-shape = refl
surplus-envelope-field : Codec.from-node table
  (C.tagged 14 (n-list [] ∷ n-list [] ∷ n-list [] ∷ [])) ≡ nothing
surplus-envelope-field = refl
bare-optional-body : Codec.from-packet table (C.tagged 11 (leaf ∷ leaf ∷ [])) ≡ nothing
bare-optional-body = refl
surplus-optional-body : Codec.from-packet table
  (C.tagged 11 (leaf ∷ n-list (leaf ∷ leaf ∷ []) ∷ [])) ≡ nothing
surplus-optional-body = refl
invalid-optional-body : Codec.from-packet table
  (C.tagged 11 (leaf ∷ n-list (n-atom 0 ∷ []) ∷ [])) ≡ nothing
invalid-optional-body = refl
missing-packet-field : Codec.from-packet table (C.tagged 11 (leaf ∷ [])) ≡ nothing
missing-packet-field = refl
missing-constructor-field : Codec.from-constructor table
  (C.tagged 12 (n-list [] ∷ n-list [] ∷ n-list [] ∷ [])) ≡ nothing
missing-constructor-field = refl
invalid-constructor-vector : Codec.from-constructor table
  (C.tagged 12 (n-list [] ∷ n-list (n-atom 0 ∷ []) ∷ n-list [] ∷ n-list [] ∷ [])) ≡ nothing
invalid-constructor-vector = refl
wrong-constructor-tag : Codec.from-constructor table (C.tagged 13 (n-list [] ∷ n-list [] ∷ n-list [] ∷ [])) ≡ nothing
wrong-constructor-tag = refl
invalid-family-constructor : Codec.from-family table
  (C.tagged 13 (n-list [] ∷ n-list [] ∷ n-list (leaf ∷ []) ∷ [])) ≡ nothing
invalid-family-constructor = refl
malformed-character-stream : Codec.decode table ('(' ∷ ';' ∷ []) ≡ nothing
malformed-character-stream = refl
trailing-character : Codec.decode table (W.encode (C.tagged 14 (n-list [] ∷ n-list [] ∷ [])) ++ (';' ∷ []))
  ≡ nothing
trailing-character = refl
missing-name-table : Codec.to-node [] payload ≡ nothing
missing-name-table = refl

-- All following envelopes DECODE, but fail native replay. Actual source
-- order, exact vector lengths and hidden raw bodies remain authoritative.
module Empty = Transport (Codec.envelope [] []) refl
empty-rejected : present (Replay.checked table Empty.characters) ≡ false
empty-rejected = Empty.status false refl
module MissingFamily = Transport (Codec.envelope [] packets) refl
missing-family-rejected : present (Replay.checked table MissingFamily.characters) ≡ false
missing-family-rejected = MissingFamily.status false refl
module MissingGlobal = Transport (Codec.envelope fixture-recipes
  (scalar-packet ∷ scalar-packet ∷ packed-packet ∷ [])) refl
missing-global-rejected : present (Replay.checked table MissingGlobal.characters) ≡ false
missing-global-rejected = MissingGlobal.status false refl
module SurplusGlobal = Transport (Codec.envelope fixture-recipes (scalar-packet ∷ packets)) refl
surplus-global-rejected : present (Replay.checked table SurplusGlobal.characters) ≡ false
surplus-global-rejected = SurplusGlobal.status false refl
module SwappedGlobals = Transport (Codec.envelope fixture-recipes
  (scalar-packet ∷ packed-packet ∷ scalar-packet ∷ unpack-packet ∷ [])) refl
swapped-global-order-rejected : present (Replay.checked table SwappedGlobals.characters) ≡ false
swapped-global-order-rejected = SwappedGlobals.status false refl
module HiddenBody = Transport (Codec.envelope fixture-recipes
  (scalar-packet ∷ packet r-leaf nothing ∷ packed-packet ∷ unpack-packet ∷ [])) refl
hidden-body-omission-rejected : present (Replay.checked table HiddenBody.characters) ≡ false
hidden-body-omission-rejected = HiddenBody.status false refl
module SwappedConstructors = Transport
  (Codec.envelope
    (Codec.family [] (r-leaf ∷ []) (Recipes.alternate-recipe ∷ Recipes.pack-recipe ∷ []) ∷ [])
    packets) refl
swapped-constructor-order-rejected : present (Replay.checked table SwappedConstructors.characters) ≡ false
swapped-constructor-order-rejected = SwappedConstructors.status false refl
module MissingConstructor = Transport
  (Codec.envelope (Codec.family [] (r-leaf ∷ []) (Recipes.pack-recipe ∷ []) ∷ []) packets) refl
missing-constructor-rejected : present (Replay.checked table MissingConstructor.characters) ≡ false
missing-constructor-rejected = MissingConstructor.status false refl
module SurplusFamily = Transport (Codec.envelope (fixture-recipes ++ fixture-recipes) packets) refl
surplus-family-rejected : present (Replay.checked table SurplusFamily.characters) ≡ false
surplus-family-rejected = SurplusFamily.status false refl

case-packet : List (List Recipe × Recipe) → Packet
case-packet branches = packet r-leaf
  (just (r-convert tm-atom_type Recipes.unpack-conversion
    (r-case (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])) [] (r-leaf ∷ []) l0
      Recipes.case-kind-recipe Recipes.case-motive-recipe branches)))
module SwappedBranches = Transport (Codec.envelope fixture-recipes
  (scalar-packet ∷ scalar-packet ∷ packed-packet ∷
    case-packet (reverse Recipes.unpack-case-branches) ∷ [])) refl
swapped-branch-order-rejected : present (Replay.checked table SwappedBranches.characters) ≡ false
swapped-branch-order-rejected = SwappedBranches.status false refl
module MissingBranches = Transport (Codec.envelope fixture-recipes
  (scalar-packet ∷ scalar-packet ∷ packed-packet ∷ case-packet [] ∷ [])) refl
missing-branches-rejected : present (Replay.checked table MissingBranches.characters) ≡ false
missing-branches-rejected = MissingBranches.status false refl

-- A name table is an input, not an authenticity certificate. Rebinding a
-- well-formed term's family slot still decodes; actual typing rejects it.
claim-recipe : Recipe
claim-recipe = r-claim E.goal (r-ctor [] [] (r-leaf ∷ r-leaf ∷ []))
claim-node : Node
claim-node = require (R.to-node table claim-recipe) refl
wrong-table : List Name
wrong-table = "" ∷ "Wrong#Family" ∷ "Boundary#Pack" ∷ "Boundary#Alternate" ∷ "payload" ∷ []
wrong-claim : Recipe
wrong-claim = r-claim (tm-data "Wrong#Family" [] (tm-atom_type ∷ []))
  (r-ctor [] [] (r-leaf ∷ r-leaf ∷ []))
wrong-table-still-parses : R.from-node wrong-table claim-node ≡ just wrong-claim
wrong-table-still-parses = refl
checked-claim : List Name → List Char → Maybe (E.N._⊢_⇒_ ⟨⟩ E.value E.goal)
checked-claim names characters with R.decode names characters
... | nothing = nothing
... | just recipe = Replay.G.D.at ⟨⟩ E.value E.goal recipe
correct-table-replays : present (checked-claim table (W.encode claim-node)) ≡ true
correct-table-replays = refl
wrong-table-rejected : present (checked-claim wrong-table (W.encode claim-node)) ≡ false
wrong-table-rejected = refl
