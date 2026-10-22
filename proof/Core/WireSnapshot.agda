------------------------------------------------------------------------
-- Complete metadata-bearing source input on the character wire.
-- Unsupported metadata is PRESERVED, not accepted or silently filtered.
-- Names are supplied table identities; no String round-trip is assumed.
------------------------------------------------------------------------
module Core.WireSnapshot where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Name; Term)
open import Core.Signature using (Ctor; Telescope; ctor-name; ctor-args; ctor-params; ctor-indices;
  nothing≠just; just-inj)
open import Core.Grade using (Grade; erased; linear; affine; unrestricted)
open import Core.Universe using (Level)
import Core.SyntaxEquality as Syntax
import Core.ExecutableSnapshot as I
import Core.Wire as W
import Core.WireRecipe as R
import Core.WireConversion as C
open import Core.WireCombinators using (both; many; optional; tagged; iso; bind)
open import Core.WireCertificate using (Codec)
open Codec
open W using (Node; n-atom; n-list)

bool-node : Bool → Node
bool-node false = n-atom 0
bool-node true = n-atom 1
node-bool : Node → Maybe Bool
node-bool (n-atom 0) = just false
node-bool (n-atom 1) = just true
node-bool other = nothing
bool-fidelity : ∀ b node → just (bool-node b) ≡ just node → node-bool node ≡ just b
bool-fidelity false node found with just-inj found
... | refl = refl
bool-fidelity true node found with just-inj found
... | refl = refl
bool : Codec Bool
bool = record { write = λ b → just (bool-node b) ; read = node-bool ; faithful = bool-fidelity }

node-grade : Node → Maybe Grade
node-grade (n-atom 0) = just erased
node-grade (n-atom 1) = just linear
node-grade (n-atom 2) = just affine
node-grade (n-atom 3) = just unrestricted
node-grade other = nothing
grade-fidelity : ∀ g node → just (n-atom (Syntax.grade-number g)) ≡ just node
  → node-grade node ≡ just g
grade-fidelity erased node found with just-inj found
... | refl = refl
grade-fidelity linear node found with just-inj found
... | refl = refl
grade-fidelity affine node found with just-inj found
... | refl = refl
grade-fidelity unrestricted node found with just-inj found
... | refl = refl
grade : Codec Grade
grade = record
  { write = λ g → just (n-atom (Syntax.grade-number g)) ; read = node-grade ; faithful = grade-fidelity }
level-fidelity : ∀ l node → just (R.level-node l) ≡ just node → R.node-level node ≡ just l
level-fidelity l node found with just-inj found
... | refl = R.level-fidelity l
level : Codec Level
level = record { write = λ l → just (R.level-node l) ; read = R.node-level ; faithful = level-fidelity }

name-read : List Name → Node → Maybe Name
name-read table (n-atom index) = W.lookup-at index table
name-read table other = nothing
name-fidelity : ∀ table name node → C.map n-atom (W.index-of name table) ≡ just node
  → name-read table node ≡ just name
name-fidelity table name node found with W.index-of name table in indexed
... | nothing = ⊥-elim (nothing≠just found)
... | just index with just-inj found
... | refl = W.index-of-sound name table index indexed
name : List Name → Codec Name
name table = record
  { write = λ value → C.map n-atom (W.index-of value table)
  ; read = name-read table ; faithful = name-fidelity table }
term : List Name → Codec Term
term table = record
  { write = W.term-to-wire table ; read = W.wire-to-term table ; faithful = W.term-fidelity table }
telescope : List Name → Codec Telescope
telescope table = many (both (name table) (term table))

declaration : List Name → Codec Ctor
declaration table = iso
  (both (name table) (both (telescope table) (both (many (term table)) (many (term table)))))
  (λ { (n , args , ps , is) → record
    { ctor-name = n ; ctor-args = args ; ctor-params = ps ; ctor-indices = is } })
  (λ c → ctor-name c , ctor-args c , ctor-params c , ctor-indices c)
  (λ c → refl)
ctor : List Name → Codec I.ConstructorInput
ctor table = tagged 15 (iso
  (both (declaration table) (both (many grade) (many bool)))
  (λ { (c , qs , es) → I.constructor-input c qs es })
  (λ c → I.ConstructorInput.declaration c , I.ConstructorInput.quantities c , I.ConstructorInput.explicit c)
  (λ c → refl))
family : List Name → Codec I.FamilyInput
family table = tagged 16 (iso
  (both (name table) (both (telescope table) (both (telescope table)
    (both level (both (many (ctor table)) bool)))))
  (λ { (n , ps , is , l , cs , o) → I.family-input n ps is l cs o })
  (λ f → I.FamilyInput.name f , I.FamilyInput.parameters f , I.FamilyInput.indices f ,
    I.FamilyInput.level f , I.FamilyInput.constructors f , I.FamilyInput.is-opaque f)
  (λ f → refl))
global : List Name → Codec I.GlobalInput
global table = tagged 17 (iso
  (both (name table) (both (term table) (both (optional (term table))
    (both (optional (many grade)) (both (optional (many bool)) (both bool bool))))))
  (λ { (n , ty , b , qs , es , c , t) → I.global-input n ty b qs es c t })
  (λ g → I.GlobalInput.name g , I.GlobalInput.type g , I.GlobalInput.body g ,
    I.GlobalInput.quantities g , I.GlobalInput.explicit g , I.GlobalInput.certified g ,
    I.GlobalInput.totality-certified g)
  (λ g → refl))
snapshot : List Name → Codec I.Input
snapshot table = tagged 18 (iso
  (both (many (family table)) (both (many (global table)) (many (both (name table) (name table)))))
  (λ { (fs , gs , bs) → I.input fs gs bs })
  (λ s → I.Input.families s , I.Input.globals s , I.Input.builtins s)
  (λ s → refl))

to-node : List Name → I.Input → Maybe Node
to-node table = write (snapshot table)
from-node : List Name → Node → Maybe I.Input
from-node table = read (snapshot table)
fidelity : ∀ table source node → to-node table source ≡ just node
  → from-node table node ≡ just source
fidelity table = faithful (snapshot table)
encode : List Name → I.Input → Maybe (List Char)
encode table source = C.map W.encode (to-node table source)
decode : List Name → List Char → Maybe I.Input
decode table characters = bind (W.decode characters) (from-node table)
character-fidelity : ∀ table source node → to-node table source ≡ just node
  → decode table (W.encode node) ≡ just source
character-fidelity table source node encoded
  rewrite W.decode-encode node = fidelity table source node encoded
roundtrip : ∀ table source characters → encode table source ≡ just characters
  → decode table characters ≡ just source
roundtrip table source characters found with to-node table source in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just node with just-inj found
... | refl = character-fidelity table source node encoded
