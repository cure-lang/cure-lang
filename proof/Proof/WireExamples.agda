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
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Core.Syntax using (Name)
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
