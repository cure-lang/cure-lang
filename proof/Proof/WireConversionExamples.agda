------------------------------------------------------------------------
-- Characters -> ConvRecipe DATA -> checked conversion of actual terms.
-- Round-trip and rejection controls do not certify an Elixir producer.
------------------------------------------------------------------------
module Proof.WireConversionExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Signature using (IndEnv)
open import Core.Reduction using (Signature)
open import Core.NativeRecipe
import Core.CanonicalSnapshot as S
import Core.Wire as W
import Core.WireConversion as Codec
import Proof.ExecutableSnapshotExamples as Snapshot
import Proof.ReductionConversion as Reduction
open W using (Node; n-atom; n-list)

present : ∀ {A : Set} → Maybe A → Bool
present nothing = false
present (just value) = true
require : ∀ {A : Set} (result : Maybe A) → present result ≡ true → A
require nothing ()
require (just value) accepted = value

table : List Name
table = "" ∷ []
recipe : ConvRecipe
recipe = c-trans tm-atom_type c-zeta (c-sym c-beta)
node : Node
node = Codec.tagged 2
  (n-list (n-atom 18 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷
    Codec.tagged 11 [] ∷ Codec.tagged 1 (Codec.tagged 10 [] ∷ []) ∷ [])
encoded-node : Codec.to-node table recipe ≡ just node
encoded-node = refl
node-roundtrip : Codec.from-node table node ≡ just recipe
node-roundtrip = Codec.fidelity table recipe node encoded-node
characters : List Char
characters = W.encode node
encoded-characters : Codec.encode table recipe ≡ just characters
encoded-characters = refl
character-roundtrip : Codec.decode table characters ≡ just recipe
character-roundtrip = Codec.roundtrip table recipe characters encoded-characters

-- One fixed character vector, independent of the codec theorem.
beta-characters : Codec.encode [] c-beta ≡ just ('(' ∷ replicate 10 '1' ++ (';' ∷ ')' ∷ []))
beta-characters = refl

sig : Signature
sig = record { body = λ _ → nothing ; type-of = λ _ → nothing }
ind : IndEnv
ind = record { families = [] ; builtins = λ _ → nothing }
module Model = Reduction.Model sig (λ ())
module Replay = Codec.Replay ind sig Model.conversion
  (λ {t} {u} → Model.reduce-converts {t = t} {u = u}) (λ ())
beta-type let-type : Term
beta-type = tm-app (tm-lam unrestricted tm-atom_type tm-atom_type) (tm-atom_lit "argument")
let-type = tm-let unrestricted tm-atom_type (tm-atom_lit "argument") tm-atom_type
checked-wire-conversion : Model._≈_ let-type beta-type
checked-wire-conversion = require (Replay.checked table let-type beta-type characters) refl

-- A well-formed recipe can fail conversion: decoding is not an oracle.
decoded-but-false-conversion : present
  (Replay.checked [] tm-atom_type tm-float_type (W.encode (Codec.tagged 0 []))) ≡ false
decoded-but-false-conversion = refl

module Actual = Codec.Replay (S.Snapshot.ind Snapshot.snapshot) (S.Snapshot.sig Snapshot.snapshot)
  Snapshot.ConversionModel.conversion
  (λ {t} {u} → Snapshot.ConversionModel.reduce-converts {t = t} {u = u})
  (λ {name} → S.Snapshot.owner-visible Snapshot.snapshot {name = name})
delta-node : Node
delta-node = Codec.tagged 12 (n-atom 0 ∷ [])
actual-visible-delta : Snapshot.ConversionModel._≈_
  (tm-global "Boundary#answer") (tm-atom_lit "answer")
actual-visible-delta = require
  (Actual.checked ("Boundary#answer" ∷ []) (tm-global "Boundary#answer")
    (tm-atom_lit "answer") (W.encode delta-node)) refl
hidden-delta-rejected : present
  (Actual.checked ("Boundary#held" ∷ []) (tm-global "Boundary#held")
    (tm-atom_lit "hidden") (W.encode delta-node)) ≡ false
hidden-delta-rejected = refl
wrong-delta-table-rejected : present
  (Actual.checked ("Boundary#held" ∷ []) (tm-global "Boundary#answer")
    (tm-atom_lit "answer") (W.encode delta-node)) ≡ false
wrong-delta-table-rejected = refl

all-constructor-shapes : List ConvRecipe
all-constructor-shapes = c-refl ∷ c-sym c-refl ∷
  c-trans tm-atom_type c-refl c-refl ∷ c-pi c-refl c-refl ∷ c-app c-refl c-refl ∷
  c-data (c-refl ∷ []) (c-refl ∷ []) ∷ c-ctor (c-refl ∷ []) ∷
  c-effect-type c-refl ∷ c-effect-pure c-refl ∷ c-effect-bind c-refl c-refl ∷
  c-beta ∷ c-zeta ∷ c-delta "" ∷ c-nat-zero ∷ c-bounded-zero ∷ c-nat-suc ∷ c-bounded-suc ∷ []
roundtrips : List ConvRecipe → Bool
roundtrips [] = true
roundtrips (child ∷ children) with Codec.to-node table child
... | nothing = false
... | just wire with Codec.from-node table wire
... | nothing = false
... | just restored = roundtrips children
all-constructors-decode : roundtrips all-constructor-shapes ≡ true
all-constructors-decode = refl

unknown-tag : Codec.from-node table (Codec.tagged 17 []) ≡ nothing
unknown-tag = refl
not-a-recipe : Codec.from-node table (n-atom 0) ≡ nothing
not-a-recipe = refl
surplus-leaf-payload : Codec.from-node table (Codec.tagged 0 (n-atom 0 ∷ [])) ≡ nothing
surplus-leaf-payload = refl
missing-child : Codec.from-node table (Codec.tagged 1 []) ≡ nothing
missing-child = refl
surplus-child : Codec.from-node table
  (Codec.tagged 1 (Codec.tagged 0 [] ∷ Codec.tagged 0 [] ∷ [])) ≡ nothing
surplus-child = refl
malformed-vector : Codec.from-node table (Codec.tagged 5 (n-atom 0 ∷ n-list [] ∷ [])) ≡ nothing
malformed-vector = refl
unknown-name-index : Codec.from-node table (Codec.tagged 12 (n-atom 1 ∷ [])) ≡ nothing
unknown-name-index = refl
absent-delta-name : Codec.to-node [] (c-delta "missing") ≡ nothing
absent-delta-name = refl
absent-payload-name : Codec.to-node table (c-trans (tm-atom_lit "missing") c-refl c-refl) ≡ nothing
absent-payload-name = refl
invalid-term-payload : Codec.from-node table
  (Codec.tagged 2
    (n-list (n-atom 25 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷ Codec.tagged 0 [] ∷ Codec.tagged 0 [] ∷ []))
  ≡ nothing
invalid-term-payload = refl
trailing-characters : Codec.decode table (characters ++ (';' ∷ [])) ≡ nothing
trailing-characters = refl
