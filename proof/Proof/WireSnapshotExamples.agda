{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- The caller supplies no constructed source. Both literal producer
-- streams are decoded and bound to checked native admission/safety.
------------------------------------------------------------------------
module Proof.WireSnapshotExamples where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Core.Syntax
open import Core.Grade using (erased; linear; affine; unrestricted)
open import Core.Universe using (l0; l2)
open import Core.Reduction using (Signature; ι; ⇝*-step; ⇝*-refl)
import Core.ExecutableSnapshot as I
import Core.CheckedAdmission as P
import Core.Wire as W
import Core.WireSnapshot as S
import Core.WireAdmission as Bundle
import Core.WireConversion as C
import Core.WireCertificate as Codec
import Core.WireCombinators as K
open Codec.Codec using (read)
open W using (Node; n-atom; n-list)
import Fixtures.ExecutableSnapshot as Fixture
import Fixtures.ExecutableBundle as Produced
import Proof.WireCertificateExamples as Recipes
import Proof.ExecutableSnapshotExamples as Source
open import Proof.CheckedAdmissionExamples using (pick; pick-equation; obtain; obtain-result)
open P using (present)

source-encoded : S.encode Produced.table Fixture.source ≡ just Produced.source-characters
source-encoded = refl
source-decoded : S.decode Produced.table Produced.source-characters ≡ just Fixture.source
source-decoded = S.roundtrip Produced.table Fixture.source Produced.source-characters source-encoded
certificate-encoded : Codec.encode Produced.table Recipes.payload ≡ just Produced.certificate-characters
certificate-encoded = refl
certificate-decoded : Codec.decode Produced.table Produced.certificate-characters ≡ just Recipes.payload
certificate-decoded =
  Codec.roundtrip Produced.table Recipes.payload Produced.certificate-characters certificate-encoded
accepted : present (Bundle.verify Produced.table Produced.source-characters Produced.certificate-characters) ≡ true
accepted = trans
  (Bundle.verify-decoded Produced.table Produced.source-characters Produced.certificate-characters
    Fixture.source source-decoded)
  (trans (P.verify-decoded Fixture.source Produced.table Produced.certificate-characters
    Recipes.payload certificate-decoded) refl)
checked : Bundle.Checked Produced.table Produced.source-characters Produced.certificate-characters
checked = obtain (Bundle.verify Produced.table Produced.source-characters Produced.certificate-characters) accepted
exact-result : Bundle.verify Produced.table Produced.source-characters Produced.certificate-characters ≡ just checked
exact-result = obtain-result
  (Bundle.verify Produced.table Produced.source-characters Produced.certificate-characters) accepted
module Pin = Bundle.Pin checked Fixture.source source-decoded
module Bodies = Pin.Bodies
source-exact : Bundle.Checked.source checked ≡ Fixture.source
source-exact = Pin.source-equal
global-table-preserved : I.global-entries (Bundle.Checked.source checked) ≡ I.global-entries Fixture.source
global-table-preserved = cong I.global-entries source-exact
family-table-preserved : I.family-entries (Bundle.Checked.source checked) ≡ I.family-entries Fixture.source
family-table-preserved = cong I.family-entries source-exact
metadata-preserved : I.metadata (Bundle.Checked.source checked) ≡ I.metadata Fixture.source
metadata-preserved = cong I.metadata source-exact

unpack : Bodies.Body "Boundary#unpack"
unpack = pick (Bodies.admit "Boundary#unpack") refl
original-goal : Bodies.Body.goal unpack ≡ tm-atom_type
original-goal = refl
safe : Pin.C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
safe = Bodies.Body.trace-safe unpack (⇝*-step (ι refl refl) ⇝*-refl)
fuel : Pin.C.Sound.FuelResult (Bodies.Body.term unpack) tm-atom_type
fuel = Bodies.Body.run unpack 2
tree : Pin.C.Sound.EvalTree (Bodies.Body.term unpack) tm-atom_type
tree = Bodies.Body.tree unpack
held : Bodies.Body "Boundary#held"
held = pick (Bodies.admit "Boundary#held") refl
hidden-raw-body-preserved : Bodies.Body.term held ≡ tm-atom_lit "hidden"
hidden-raw-body-preserved = refl
hidden-stays-hidden : Signature.body Pin.C.W.sig "Boundary#held" ≡ nothing
hidden-stays-hidden = refl

module Encoded (source : I.Input) (written : present (S.to-node Produced.table source) ≡ true) where
  node : Node
  node = pick (S.to-node Produced.table source) written
  node-written : S.to-node Produced.table source ≡ just node
  node-written = pick-equation (S.to-node Produced.table source) written
  characters : List Char
  characters = W.encode node
  decoded : S.decode Produced.table characters ≡ just source
  decoded = S.character-fidelity Produced.table source node node-written
  status : ∀ expected → P.data-status source Recipes.payload ≡ expected
    → present (Bundle.verify Produced.table characters Produced.certificate-characters) ≡ expected
  status expected success = trans
    (Bundle.verify-decoded Produced.table characters Produced.certificate-characters source decoded)
    (trans (P.verify-decoded source Produced.table Produced.certificate-characters
      Recipes.payload certificate-decoded) success)

-- Exercise ALL metadata carriers, including semantically unsupported
-- values, grades and nonempty builtins. The codec must preserve these.
metadata-source : I.Input
metadata-source = I.input
  (I.family-input "Boundary#Packed" (("A" , tm-type l0) ∷ []) (("x" , tm-var 0) ∷ []) l2
    (I.constructor-input
      (record { ctor-name = "Boundary#Pack" ; ctor-args = ("x" , tm-var 0) ∷ []
              ; ctor-params = tm-var 1 ∷ [] ; ctor-indices = tm-var 0 ∷ [] })
      (erased ∷ linear ∷ affine ∷ unrestricted ∷ []) (false ∷ true ∷ []) ∷ []) true ∷ [])
  (I.global-input "Boundary#held" tm-atom_type (just (tm-atom_lit "hidden"))
      (just []) (just (false ∷ true ∷ [])) false true ∷
   I.global-input "Boundary#answer" tm-float_type nothing nothing nothing true false ∷ [])
  (("A" , "Boundary#Packed") ∷ [])
module Metadata = Encoded metadata-source refl
all-metadata-roundtrip : S.decode Produced.table Metadata.characters ≡ just metadata-source
all-metadata-roundtrip = Metadata.decoded
unsupported-metadata-rejected :
  present (Bundle.verify Produced.table Metadata.characters Produced.certificate-characters) ≡ false
unsupported-metadata-rejected = Metadata.status false refl
module Duplicate = Encoded Source.duplicate-families refl
duplicate-source-rejected :
  present (Bundle.verify Produced.table Duplicate.characters Produced.certificate-characters) ≡ false
duplicate-source-rejected = Duplicate.status false refl
changed-source : I.Input
changed-source = record Fixture.source
  { globals = record Source.raw-answer { type = tm-float_type } ∷
    Source.raw-held ∷ Source.raw-packed ∷ Source.raw-unpack ∷ [] }
module Changed = Encoded changed-source refl
source-certificate-mismatch :
  present (Bundle.verify Produced.table Changed.characters Produced.certificate-characters) ≡ false
source-certificate-mismatch = Changed.status false refl

invalid-bool : read S.bool (n-atom 2) ≡ nothing
invalid-bool = refl
invalid-grade : read S.grade (n-atom 4) ≡ nothing
invalid-grade = refl
invalid-level : read S.level (n-atom 3) ≡ nothing
invalid-level = refl
short-product : read (K.both S.bool S.bool) (n-list (n-atom 0 ∷ [])) ≡ nothing
short-product = refl
bare-optional : read (K.optional S.bool) (n-atom 0) ≡ nothing
bare-optional = refl
surplus-optional : read (K.optional S.bool) (n-list (n-atom 0 ∷ n-atom 1 ∷ [])) ≡ nothing
surplus-optional = refl
absent-layout : read (K.optional (K.many S.grade)) (n-list []) ≡ just nothing
absent-layout = refl
present-empty-layout : read (K.optional (K.many S.grade)) (n-list (n-list [] ∷ [])) ≡ just (just [])
present-empty-layout = refl
missing-name : S.to-node [] Fixture.source ≡ nothing
missing-name = refl
out-of-range-name : read (S.name []) (n-atom 0) ≡ nothing
out-of-range-name = refl
wrong-record-tag : S.from-node Produced.table (C.tagged 17 (n-list [] ∷ [])) ≡ nothing
wrong-record-tag = refl
surplus-record-child : S.from-node Produced.table (C.tagged 18 (n-list [] ∷ n-list [] ∷ [])) ≡ nothing
surplus-record-child = refl
malformed-source-characters :
  present (Bundle.verify Produced.table ('(' ∷ []) Produced.certificate-characters) ≡ false
malformed-source-characters = refl
malformed-certificate :
  present (Bundle.verify [] (W.encode (C.tagged 18
    (n-list (n-list [] ∷ n-list (n-list [] ∷ n-list [] ∷ []) ∷ []) ∷ []))) ('(' ∷ [])) ≡ false
malformed-certificate = refl
-- A small empty source pins trailing-root rejection without re-scanning
-- the full literal fixture in every malformed control.
empty-source : I.Input
empty-source = I.input [] [] []
empty-character-vector : S.encode [] empty-source ≡
  just ('(' ∷ W.unary 18 ++ toList ";(()(()())))")
empty-character-vector = refl
empty-node : Node
empty-node = pick (S.to-node [] empty-source) refl
trailing-source : S.decode [] (W.encode empty-node ++ (';' ∷ [])) ≡ nothing
trailing-source = refl
