------------------------------------------------------------------------
-- Recipe data fidelity is independent of semantic replay. These shapes
-- cover every constructor, including nonempty term/recipe/branch vectors.
------------------------------------------------------------------------
module Proof.WireRecipeExamples where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Universe using (l0; l1; l2)
open import Core.NativeRecipe
import Core.Wire as W
import Core.WireRecipe as R
import Core.WireConversion as C
open W using (Node; n-atom; n-list)

table : List Name
table = "" ∷ "payload" ∷ []
leaf : Node
leaf = C.tagged 0 []
shapes : List Recipe
shapes =
  r-leaf ∷ r-pi r-leaf r-leaf ∷ r-lam r-leaf r-leaf ∷ r-app r-leaf r-leaf ∷
  r-let r-leaf r-leaf r-leaf ∷ r-data (r-leaf ∷ []) (r-leaf ∷ []) ∷
  r-ctor (tm-atom_lit "payload" ∷ []) (r-leaf ∷ []) (r-leaf ∷ []) ∷
  r-claim tm-atom_type r-leaf ∷ r-cumul l0 r-leaf ∷ r-cumul l1 r-leaf ∷ r-cumul l2 r-leaf ∷
  r-convert tm-atom_type (c-trans tm-atom_type c-refl c-refl) r-leaf ∷
  r-case r-leaf (r-leaf ∷ []) (r-leaf ∷ []) l0 r-leaf r-leaf
    (((r-leaf ∷ []) , r-claim tm-atom_type r-leaf) ∷
     ([] , r-case r-leaf [] [] l2 r-leaf r-leaf []) ∷ []) ∷ []

-- Explicit nodes, not just an assertion that decoding returned something.
shape-nodes : List Node
shape-nodes =
  leaf ∷ C.tagged 1 (leaf ∷ leaf ∷ []) ∷ C.tagged 2 (leaf ∷ leaf ∷ []) ∷
  C.tagged 3 (leaf ∷ leaf ∷ []) ∷ C.tagged 4 (leaf ∷ leaf ∷ leaf ∷ []) ∷
  C.tagged 5 (n-list (leaf ∷ []) ∷ n-list (leaf ∷ []) ∷ []) ∷
  C.tagged 6
    (n-list (n-list (n-atom 19 ∷ n-atom 1 ∷ n-atom 0 ∷ []) ∷ []) ∷
      n-list (leaf ∷ []) ∷ n-list (leaf ∷ []) ∷ []) ∷
  C.tagged 7 (n-list (n-atom 18 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷ leaf ∷ []) ∷
  C.tagged 8 (n-atom 0 ∷ leaf ∷ []) ∷ C.tagged 8 (n-atom 1 ∷ leaf ∷ []) ∷
  C.tagged 8 (n-atom 2 ∷ leaf ∷ []) ∷
  C.tagged 9
    (n-list (n-atom 18 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷
      C.tagged 2 (n-list (n-atom 18 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷ leaf ∷ leaf ∷ []) ∷ leaf ∷ []) ∷
  C.tagged 10
    (leaf ∷ n-list (leaf ∷ []) ∷ n-list (leaf ∷ []) ∷ n-atom 0 ∷ leaf ∷ leaf ∷
      n-list
        (n-list (n-list (leaf ∷ []) ∷
          C.tagged 7 (n-list (n-atom 18 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷ leaf ∷ []) ∷ []) ∷
         n-list (n-list [] ∷
           C.tagged 10 (leaf ∷ n-list [] ∷ n-list [] ∷ n-atom 2 ∷ leaf ∷ leaf ∷ n-list [] ∷ []) ∷ []) ∷ []) ∷ []) ∷ []
all-shapes-encode : R.to-nodes table shapes ≡ just shape-nodes
all-shapes-encode = refl
all-shapes-fidelity : R.from-nodes table shape-nodes ≡ just shapes
all-shapes-fidelity = R.each-fidelity table shapes shape-nodes all-shapes-encode

-- An independently pinned literal character vector.
leaf-characters : R.encode [] r-leaf ≡ just ('(' ∷ ';' ∷ ')' ∷ [])
leaf-characters = refl
case-shape : Recipe
case-shape = r-case r-leaf [] [] l1 r-leaf r-leaf (([] , r-leaf) ∷ [])
case-node : Node
case-node = C.tagged 10
  (leaf ∷ n-list [] ∷ n-list [] ∷ n-atom 1 ∷ leaf ∷ leaf ∷
    n-list (n-list (n-list [] ∷ leaf ∷ []) ∷ []) ∷ [])
case-encoded : R.to-node table case-shape ≡ just case-node
case-encoded = refl
characters : List Char
characters = W.encode case-node
case-character-fidelity : R.decode table characters ≡ just case-shape
case-character-fidelity = R.roundtrip table case-shape characters refl

unknown-tag : R.from-node table (C.tagged 11 []) ≡ nothing
unknown-tag = refl
bare-atom : R.from-node table (n-atom 0) ≡ nothing
bare-atom = refl
surplus-leaf : R.from-node table (C.tagged 0 (leaf ∷ [])) ≡ nothing
surplus-leaf = refl
missing-child : R.from-node table (C.tagged 1 (leaf ∷ [])) ≡ nothing
missing-child = refl
surplus-child : R.from-node table (C.tagged 2 (leaf ∷ leaf ∷ leaf ∷ [])) ≡ nothing
surplus-child = refl
malformed-recipe-vector : R.from-node table (C.tagged 5 (n-atom 0 ∷ n-list [] ∷ [])) ≡ nothing
malformed-recipe-vector = refl
malformed-term-vector : R.from-node table
  (C.tagged 6 (n-list (n-atom 0 ∷ []) ∷ n-list [] ∷ n-list [] ∷ [])) ≡ nothing
malformed-term-vector = refl
invalid-term-payload : R.from-node table
  (C.tagged 7 (n-list (n-atom 0 ∷ n-atom 0 ∷ n-atom 3 ∷ []) ∷ leaf ∷ [])) ≡ nothing
invalid-term-payload = refl
invalid-conversion-payload : R.from-node table
  (C.tagged 9 (n-list (n-atom 18 ∷ n-atom 0 ∷ n-atom 0 ∷ []) ∷ C.tagged 17 [] ∷ leaf ∷ [])) ≡ nothing
invalid-conversion-payload = refl
missing-name : R.to-node table (r-claim (tm-atom_lit "missing") r-leaf) ≡ nothing
missing-name = refl
missing-vector-name : R.to-node table (r-ctor (tm-atom_lit "missing" ∷ []) [] []) ≡ nothing
missing-vector-name = refl
out-of-range-name : R.from-node table
  (C.tagged 7 (n-list (n-atom 19 ∷ n-atom 2 ∷ n-atom 0 ∷ []) ∷ leaf ∷ [])) ≡ nothing
out-of-range-name = refl
invalid-cumulative-level : R.from-node table (C.tagged 8 (n-atom 3 ∷ leaf ∷ [])) ≡ nothing
invalid-cumulative-level = refl
non-atomic-level : R.from-node table (C.tagged 8 (n-list [] ∷ leaf ∷ [])) ≡ nothing
non-atomic-level = refl
bad-case : Node → Node → Node
bad-case level branches = C.tagged 10
  (leaf ∷ n-list [] ∷ n-list [] ∷ level ∷ leaf ∷ leaf ∷ branches ∷ [])
invalid-case-level : R.from-node table (bad-case (n-atom 3) (n-list [])) ≡ nothing
invalid-case-level = refl
missing-case-field : R.from-node table
  (C.tagged 10 (leaf ∷ n-list [] ∷ n-list [] ∷ n-atom 0 ∷ leaf ∷ leaf ∷ [])) ≡ nothing
missing-case-field = refl
surplus-case-field : R.from-node table
  (C.tagged 10 (leaf ∷ n-list [] ∷ n-list [] ∷ n-atom 0 ∷ leaf ∷ leaf ∷ n-list [] ∷ leaf ∷ [])) ≡ nothing
surplus-case-field = refl
swapped-case-fields : R.from-node table
  (C.tagged 10 (n-list [] ∷ leaf ∷ n-list [] ∷ n-atom 0 ∷ leaf ∷ leaf ∷ n-list [] ∷ [])) ≡ nothing
swapped-case-fields = refl
bare-branch-vector : R.from-node table (bad-case (n-atom 0) (n-atom 0)) ≡ nothing
bare-branch-vector = refl
missing-branch-body : R.from-node table
  (bad-case (n-atom 0) (n-list (n-list (n-list [] ∷ []) ∷ []))) ≡ nothing
missing-branch-body = refl
surplus-branch-body : R.from-node table
  (bad-case (n-atom 0) (n-list (n-list (n-list [] ∷ leaf ∷ leaf ∷ []) ∷ []))) ≡ nothing
surplus-branch-body = refl
invalid-branch-kind : R.from-node table
  (bad-case (n-atom 0) (n-list (n-list (n-list (n-atom 0 ∷ []) ∷ leaf ∷ []) ∷ []))) ≡ nothing
invalid-branch-kind = refl
trailing-character : R.decode table (characters ++ (';' ∷ [])) ≡ nothing
trailing-character = refl
