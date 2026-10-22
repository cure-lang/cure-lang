------------------------------------------------------------------------
-- Concrete wire-format instances and rejection controls.
--
-- The codec itself is in Core.Wire: decoding an instruction stream is
-- proved to invert `instructions`, the character rendering is proved to
-- determine each instruction, and interning is proved to return the name
-- that was written. Nothing here is a proof about an Elixir producer.
------------------------------------------------------------------------
module Proof.WireExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Core.Syntax using (Name; Term; tm-atom_lit)
open import Core.Wire

decision : ∀ {A : Set} → Maybe A → Bool
decision (just value) = true
decision nothing = false

------------------------------------------------------------------------
-- A worked example: `( ( 1 ) 0 )` as a tree
------------------------------------------------------------------------

example : Node
example = n-list (n-atom 1 ∷ n-list [] ∷ n-atom 0 ∷ [])

example-instructions : List Instr
example-instructions = instructions example

-- The flattening is the expected instruction stream, definitionally.
example-flattening : example-instructions ≡
  i-open ∷ i-atom 1 ∷ i-open ∷ i-close ∷ i-atom 0 ∷ i-close ∷ []
example-flattening = refl

example-decodes : run example-instructions ≡ just example
example-decodes = run-instructions example

-- And it renders to exactly these characters: each list is bracketed,
-- each atom is a unary run terminated by ';'.
example-rendering : render-items example-instructions ≡
  '(' ∷ '1' ∷ ';' ∷ '(' ∷ ')' ∷ ';' ∷ ')' ∷ []
example-rendering = refl

------------------------------------------------------------------------
-- Rejection controls: the machine refuses malformed streams
------------------------------------------------------------------------

stray-close : run (i-close ∷ []) ≡ nothing
stray-close = refl
unclosed-list : run (i-open ∷ []) ≡ nothing
unclosed-list = refl
trailing-junk : run (i-atom 0 ∷ i-close ∷ []) ≡ nothing
trailing-junk = refl
nested-unclosed : run (i-open ∷ i-atom 0 ∷ []) ≡ nothing
nested-unclosed = refl

------------------------------------------------------------------------
-- Character unambiguity controls
------------------------------------------------------------------------

-- Two different instructions can never render to the same characters.
distinct-instructions : i-atom 1 ≢ i-open
distinct-instructions eq with render-injective (i-atom 1) i-open (cong render eq)
... | ()

distinct-close : i-close ≢ i-atom 0
distinct-close eq with render-injective i-close (i-atom 0) (cong render eq)
... | ()

same-instruction : render-injective (i-atom 3) (i-atom 3) refl ≡ refl
same-instruction = refl

------------------------------------------------------------------------
-- Interning: a written index decodes to the name that was written, and a
-- name absent from the table cannot be interned at all.
------------------------------------------------------------------------

table : List Name
table = "a" ∷ "b" ∷ []

first-index : index-of "a" table ≡ just zero
first-index = refl
second-index : index-of "b" table ≡ just (suc zero)
second-index = refl
absent-name : decision (index-of "c" table) ≡ false
absent-name = refl

-- The soundness direction used by a decoder: what was written is read back.
second-lookup : lookup-at (suc zero) table ≡ just "b"
second-lookup = index-of-sound "b" table (suc zero) second-index

------------------------------------------------------------------------
-- The character-level scanner
------------------------------------------------------------------------

example-characters : List Char
example-characters = '(' ∷ '1' ∷ ';' ∷ '(' ∷ ')' ∷ ';' ∷ ')' ∷ []

example-encoded : encode example ≡ example-characters
example-encoded = example-rendering

-- Scanning the characters recovers the instruction stream …
example-scanned : scan example-characters ≡ just example-instructions
example-scanned = scan-encode example-instructions

-- … and the whole codec decodes the worked example back to its tree.
example-decoded : decode example-characters ≡ just example
example-decoded = decode-encode example

-- Every tree round-trips through the characters.
roundtrip : ∀ node → decode (encode node) ≡ just node
roundtrip = decode-encode

------------------------------------------------------------------------
-- Scanner rejection controls
------------------------------------------------------------------------

garbage-character : scan ('x' ∷ []) ≡ nothing
garbage-character = refl
unterminated-run : scan ('1' ∷ []) ≡ nothing
unterminated-run = refl
garbage-after-atom : scan (';' ∷ 'x' ∷ []) ≡ nothing
garbage-after-atom = refl

-- A closed empty list IS a tree …
empty-list-decodes : decode ('(' ∷ ')' ∷ []) ≡ just (n-list [])
empty-list-decodes = refl

-- … but a list that never closes is rejected although every character is
-- legal and the scan itself succeeds.
unclosed-tree : decode ('(' ∷ '1' ∷ ';' ∷ []) ≡ nothing
unclosed-tree = refl

-- The root is complete before the stream ends.
trailing-close : decode (';' ∷ ')' ∷ []) ≡ nothing
trailing-close = refl

------------------------------------------------------------------------
-- Reflected terms on the wire
--
-- Terms travel as the existing proved `Code` reflection, with names
-- interned. `atom-literals` uses a one-name table so the wire node is
-- checkable by computation.
------------------------------------------------------------------------

name-table : List Name
name-table = "a" ∷ []

atom-wire : Node
atom-wire = n-list (n-atom 19 ∷ n-atom 0 ∷ n-atom 0 ∷ [])

example-term : Term
example-term = tm-atom_lit "a"

example-term-wire : term-to-wire name-table example-term ≡ just atom-wire
example-term-wire = refl

-- The wire node decodes back to the term it came from.
example-term-decoded : wire-to-term name-table atom-wire ≡ just example-term
example-term-decoded =
  term-fidelity name-table example-term atom-wire example-term-wire

-- And the whole character pipeline does too: characters → tree → term.
example-term-characters : decode-term name-table (encode atom-wire)
  ≡ just example-term
example-term-characters =
  decode-term-fidelity name-table example-term atom-wire example-term-wire

------------------------------------------------------------------------
-- Payload rejection controls
------------------------------------------------------------------------

-- A name absent from the table cannot be written at all.
absent-name-term : decision (term-to-wire [] example-term) ≡ false
absent-name-term = refl

-- An out-of-range table index cannot be read.
index-out-of-range : decision
  (wire-to-term name-table (n-list (n-atom 19 ∷ n-atom 5 ∷ n-atom 0 ∷ []))) ≡ false
index-out-of-range = refl

-- A node that is not a reflected code (a bare atom) is rejected.
not-a-code : decision (wire-to-term name-table (n-atom 19)) ≡ false
not-a-code = refl

-- A code node with a truncated payload is rejected.
truncated-code : decision
  (wire-to-term name-table (n-list (n-atom 19 ∷ n-atom 0 ∷ []))) ≡ false
truncated-code = refl

------------------------------------------------------------------------
-- The SHARED CROSS-LANGUAGE VECTOR.
--
-- `Cure.Core.ProofWire` (the Elixir producer) and this codec pin the SAME
-- characters for `tm-atom_lit "a"` under the table `["" , "a"]`:
-- `(1111111111111111111;1;;)`. The Elixir side asserts the string in
-- `test/cure/core/proof_wire_test.exs`; the producer itself is unverified
-- code, and this vector is the hand-checked artifact they share.
------------------------------------------------------------------------

cross-table : List Name
cross-table = "" ∷ "a" ∷ []

cross-node : Node
cross-node = n-list (n-atom 19 ∷ n-atom 1 ∷ n-atom 0 ∷ [])

cross-wire : term-to-wire cross-table (tm-atom_lit "a") ≡ just cross-node
cross-wire = refl

cross-characters : encode cross-node ≡
  '(' ∷ replicate 19 '1' ++ (';' ∷ '1' ∷ ';' ∷ ';' ∷ ')' ∷ [])
cross-characters = refl

cross-decodes : decode-term cross-table (encode cross-node) ≡ just (tm-atom_lit "a")
cross-decodes = decode-term-fidelity cross-table (tm-atom_lit "a") cross-node cross-wire
