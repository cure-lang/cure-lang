------------------------------------------------------------------------
-- Proof-free certificate containers. Tags 11--14 are packet, constructor,
-- family and envelope. Source declarations/terms are NOT payload fields.
-- Only checked semantic replay can turn decoded data into native evidence.
------------------------------------------------------------------------
module Core.WireCertificate where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Name)
open import Core.Signature using (nothing≠just; just-inj)
open import Core.NativeRecipe using (Recipe; Packet; packet; ConstructorRecipe; FamilyRecipe)
open import Core.Typing using (Conversion)
open import Core.Reduction using (_⇝_)
import Core.NativeRecipe as Native
import Core.ExecutableSnapshot as Input
import Core.ExecutableReplay as Payloads
import Core.CanonicalSnapshot as S
import Core.Wire as W
import Core.WireRecipe as R
import Core.WireConversion as C
open W using (Node; n-atom; n-list)

-- Generic list transport is used only outside recursive Recipe traversal.
record Codec (A : Set) : Set where
  field
    write : A → Maybe Node
    read : Node → Maybe A
    faithful : ∀ value node → write value ≡ just node → read node ≡ just value

module Vector {A : Set} (codec : Codec A) where
  open Codec codec
  write-list : List A → Maybe (List Node)
  write-list [] = just []
  write-list (a ∷ as) = C.pair _∷_ (write a) (write-list as)
  read-list : List Node → Maybe (List A)
  read-list [] = just []
  read-list (n ∷ ns) = C.pair _∷_ (read n) (read-list ns)
  list-fidelity : ∀ values nodes → write-list values ≡ just nodes → read-list nodes ≡ just values
  list-fidelity [] nodes found with just-inj found
  ... | refl = refl
  list-fidelity (a ∷ as) nodes found with write a in ea
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just na with write-list as in eas
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nas with just-inj found
  ... | refl rewrite faithful a na ea | list-fidelity as nas eas = refl

to-body : List Name → Maybe Recipe → Maybe Node
to-body table nothing = just (n-list [])
to-body table (just recipe) = C.map (λ n → n-list (n ∷ [])) (R.to-node table recipe)
from-body : List Name → Node → Maybe (Maybe Recipe)
from-body table (n-list []) = just nothing
from-body table (n-list (node ∷ [])) = C.map just (R.from-node table node)
from-body table other = nothing
body-fidelity : ∀ table body node → to-body table body ≡ just node
  → from-body table node ≡ just body
body-fidelity table nothing node found with just-inj found
... | refl = refl
body-fidelity table (just recipe) node found with R.to-node table recipe in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just n with just-inj found
... | refl rewrite R.fidelity table recipe n encoded = refl

to-packet : List Name → Packet → Maybe Node
to-packet table (packet kind body) = C.two 11 (R.to-node table kind) (to-body table body)
from-packet : List Name → Node → Maybe Packet
from-packet table (n-list (n-atom 11 ∷ kind ∷ body ∷ [])) =
  C.pair packet (R.from-node table kind) (from-body table body)
from-packet table other = nothing
packet-fidelity : ∀ table value node → to-packet table value ≡ just node
  → from-packet table node ≡ just value
packet-fidelity table (packet kind body) node found with R.to-node table kind in ek
... | nothing = ⊥-elim (nothing≠just found)
... | just nk with to-body table body in eb
... | nothing = ⊥-elim (nothing≠just found)
... | just nb with just-inj found
... | refl rewrite R.fidelity table kind nk ek | body-fidelity table body nb eb = refl
packet-codec : List Name → Codec Packet
packet-codec table = record
  { write = to-packet table ; read = from-packet table ; faithful = packet-fidelity table }

constructor-recipe : List Recipe → List Recipe → List Recipe → List Recipe → ConstructorRecipe
constructor-recipe ps fs rps ris = record
  { ctor-parameter-recipes = ps ; ctor-field-recipes = fs
  ; ctor-result-parameter-recipes = rps ; ctor-result-index-recipes = ris }
to-constructor : List Name → ConstructorRecipe → Maybe Node
to-constructor table value = R.fields 12
  (C.map n-list (R.to-nodes table (ConstructorRecipe.ctor-parameter-recipes value)) ∷
   C.map n-list (R.to-nodes table (ConstructorRecipe.ctor-field-recipes value)) ∷
   C.map n-list (R.to-nodes table (ConstructorRecipe.ctor-result-parameter-recipes value)) ∷
   C.map n-list (R.to-nodes table (ConstructorRecipe.ctor-result-index-recipes value)) ∷ [])
from-constructor : List Name → Node → Maybe ConstructorRecipe
from-constructor table (n-list (n-atom 12 ∷ n-list ps ∷ n-list fs ∷ n-list rps ∷ n-list ris ∷ []))
  with R.from-nodes table ps | R.from-nodes table fs | R.from-nodes table rps | R.from-nodes table ris
... | just p | just f | just rp | just ri = just (constructor-recipe p f rp ri)
... | _ | _ | _ | _ = nothing
from-constructor table other = nothing
constructor-fidelity : ∀ table value node → to-constructor table value ≡ just node
  → from-constructor table node ≡ just value
constructor-fidelity table value node found
  with R.to-nodes table (ConstructorRecipe.ctor-parameter-recipes value) in ep
... | nothing = ⊥-elim (nothing≠just found)
... | just np with R.to-nodes table (ConstructorRecipe.ctor-field-recipes value) in ef
... | nothing = ⊥-elim (nothing≠just found)
... | just nf with R.to-nodes table (ConstructorRecipe.ctor-result-parameter-recipes value) in erp
... | nothing = ⊥-elim (nothing≠just found)
... | just nrp with R.to-nodes table (ConstructorRecipe.ctor-result-index-recipes value) in eri
... | nothing = ⊥-elim (nothing≠just found)
... | just nri with just-inj found
... | refl
  rewrite R.each-fidelity table (ConstructorRecipe.ctor-parameter-recipes value) np ep
    | R.each-fidelity table (ConstructorRecipe.ctor-field-recipes value) nf ef
    | R.each-fidelity table (ConstructorRecipe.ctor-result-parameter-recipes value) nrp erp
    | R.each-fidelity table (ConstructorRecipe.ctor-result-index-recipes value) nri eri = refl
constructor-codec : List Name → Codec ConstructorRecipe
constructor-codec table = record
  { write = to-constructor table ; read = from-constructor table ; faithful = constructor-fidelity table }

family : List Recipe → List Recipe → List ConstructorRecipe → FamilyRecipe
family ps is cs = record
  { fam-parameter-recipes = ps ; fam-index-recipes = is ; fam-constructor-recipes = cs }
to-family : List Name → FamilyRecipe → Maybe Node
to-family table value = C.three 13
  (C.map n-list (R.to-nodes table (FamilyRecipe.fam-parameter-recipes value)))
  (C.map n-list (R.to-nodes table (FamilyRecipe.fam-index-recipes value)))
  (C.map n-list (Vector.write-list (constructor-codec table) (FamilyRecipe.fam-constructor-recipes value)))
from-family : List Name → Node → Maybe FamilyRecipe
from-family table (n-list (n-atom 13 ∷ n-list ps ∷ n-list is ∷ n-list cs ∷ [])) =
  C.triple family (R.from-nodes table ps) (R.from-nodes table is)
    (Vector.read-list (constructor-codec table) cs)
from-family table other = nothing
family-fidelity : ∀ table value node → to-family table value ≡ just node
  → from-family table node ≡ just value
family-fidelity table value node found
  with R.to-nodes table (FamilyRecipe.fam-parameter-recipes value) in ep
... | nothing = ⊥-elim (nothing≠just found)
... | just np with R.to-nodes table (FamilyRecipe.fam-index-recipes value) in ei
... | nothing = ⊥-elim (nothing≠just found)
... | just ni
  with Vector.write-list (constructor-codec table) (FamilyRecipe.fam-constructor-recipes value) in ec
... | nothing = ⊥-elim (nothing≠just found)
... | just nc with just-inj found
... | refl
  rewrite R.each-fidelity table (FamilyRecipe.fam-parameter-recipes value) np ep
    | R.each-fidelity table (FamilyRecipe.fam-index-recipes value) ni ei
    | Vector.list-fidelity (constructor-codec table) (FamilyRecipe.fam-constructor-recipes value) nc ec = refl
family-codec : List Name → Codec FamilyRecipe
family-codec table = record
  { write = to-family table ; read = from-family table ; faithful = family-fidelity table }

record Envelope : Set where
  constructor envelope
  field
    families : List FamilyRecipe
    packets : List Packet
to-node : List Name → Envelope → Maybe Node
to-node table (envelope fs ps) = C.two 14
  (C.map n-list (Vector.write-list (family-codec table) fs))
  (C.map n-list (Vector.write-list (packet-codec table) ps))
from-node : List Name → Node → Maybe Envelope
from-node table (n-list (n-atom 14 ∷ n-list fs ∷ n-list ps ∷ [])) =
  C.pair envelope (Vector.read-list (family-codec table) fs) (Vector.read-list (packet-codec table) ps)
from-node table other = nothing
fidelity : ∀ table value node → to-node table value ≡ just node
  → from-node table node ≡ just value
fidelity table (envelope fs ps) node found with Vector.write-list (family-codec table) fs in ef
... | nothing = ⊥-elim (nothing≠just found)
... | just nf with Vector.write-list (packet-codec table) ps in ep
... | nothing = ⊥-elim (nothing≠just found)
... | just np with just-inj found
... | refl rewrite Vector.list-fidelity (family-codec table) fs nf ef
    | Vector.list-fidelity (packet-codec table) ps np ep = refl
encode : List Name → Envelope → Maybe (List Char)
encode table value = C.map W.encode (to-node table value)
decode : List Name → List Char → Maybe Envelope
decode table characters with W.decode characters
... | nothing = nothing
... | just node = from-node table node
character-fidelity : ∀ table value node → to-node table value ≡ just node
  → decode table (W.encode node) ≡ just value
character-fidelity table value node found
  rewrite W.decode-encode node | fidelity table value node found = refl
roundtrip : ∀ table value characters → encode table value ≡ just characters
  → decode table characters ≡ just value
roundtrip table value characters found with to-node table value in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just node with just-inj found
... | refl = character-fidelity table value node encoded

module Replay (source : Input.Input) (metadata : Input.Accepted source)
  (payloads : Payloads.Replay.Payloads source metadata) (conv : Conversion)
  (reduce : ∀ {t u} → _⇝_ (S.Snapshot.sig (Payloads.Replay.snapshot source metadata)) t u
    → Conversion._≈_ conv t u) where
  module G = Native.Globals source metadata payloads conv reduce
  checked : List Name → List Char → Maybe G.C.Evidence
  checked table characters with decode table characters
  ... | nothing = nothing
  ... | just (envelope fs ps) = G.certificate fs ps

  -- The equality is only transport through the parser, NOT acceptance.
  -- The right side still runs the native certificate checker.
  checked-fidelity : ∀ table value node → to-node table value ≡ just node
    → checked table (W.encode node) ≡ G.certificate (Envelope.families value) (Envelope.packets value)
  checked-fidelity table value node found rewrite character-fidelity table value node found = refl
