------------------------------------------------------------------------
-- All current ConvRecipe constructors on the character wire.
-- Decoding produces DATA, never a conversion proof. Actual conversion
-- is still checked by NativeRecipe.Derive.conversion.
-- Term payloads use Wire's canonical validator; delta names are interned.
------------------------------------------------------------------------
module Core.WireConversion where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax using (Name; Term)
open import Core.Signature using (IndEnv; findCtor; findFamily; fam-name; nothing≠just; just-inj)
open import Core.Reduction using (Signature; _⇝_)
open import Core.Typing using (Conversion)
open import Data.Product using (_,_)
open import Core.NativeRecipe using (ConvRecipe; c-refl; c-sym; c-trans; c-pi; c-app;
  c-data; c-ctor; c-effect-type; c-effect-pure; c-effect-bind; c-beta; c-zeta;
  c-delta; c-nat-zero; c-bounded-zero; c-nat-suc; c-bounded-suc)
import Core.Wire as W
open W using (Node; n-list; n-atom)

map : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
map f nothing = nothing
map f (just value) = just (f value)
pair : ∀ {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
pair f (just a) (just b) = just (f a b)
pair f _ _ = nothing
triple : ∀ {A B C D : Set} → (A → B → C → D) → Maybe A → Maybe B → Maybe C → Maybe D
triple f (just a) (just b) (just c) = just (f a b c)
triple f _ _ _ = nothing

tagged : ℕ → List Node → Node
tagged tag children = n-list (n-atom tag ∷ children)
one : ℕ → Maybe Node → Maybe Node
one tag = map (λ a → tagged tag (a ∷ []))
two : ℕ → Maybe Node → Maybe Node → Maybe Node
two tag = pair (λ a b → tagged tag (a ∷ b ∷ []))
three : ℕ → Maybe Node → Maybe Node → Maybe Node → Maybe Node
three tag = triple (λ a b c → tagged tag (a ∷ b ∷ c ∷ []))

mutual
  to-node : List Name → ConvRecipe → Maybe Node
  to-node table c-refl = just (tagged 0 [])
  to-node table (c-sym child) = one 1 (to-node table child)
  to-node table (c-trans middle left right) =
    three 2 (W.term-to-wire table middle) (to-node table left) (to-node table right)
  to-node table (c-pi left right) = two 3 (to-node table left) (to-node table right)
  to-node table (c-app left right) = two 4 (to-node table left) (to-node table right)
  to-node table (c-data ps is) =
    two 5 (map n-list (to-nodes table ps)) (map n-list (to-nodes table is))
  to-node table (c-ctor children) = one 6 (map n-list (to-nodes table children))
  to-node table (c-effect-type child) = one 7 (to-node table child)
  to-node table (c-effect-pure child) = one 8 (to-node table child)
  to-node table (c-effect-bind left right) = two 9 (to-node table left) (to-node table right)
  to-node table c-beta = just (tagged 10 [])
  to-node table c-zeta = just (tagged 11 [])
  to-node table (c-delta name) with W.index-of name table
  ... | nothing = nothing
  ... | just index = just (tagged 12 (n-atom index ∷ []))
  to-node table c-nat-zero = just (tagged 13 [])
  to-node table c-bounded-zero = just (tagged 14 [])
  to-node table c-nat-suc = just (tagged 15 [])
  to-node table c-bounded-suc = just (tagged 16 [])

  to-nodes : List Name → List ConvRecipe → Maybe (List Node)
  to-nodes table [] = just []
  to-nodes table (child ∷ children) = pair _∷_ (to-node table child) (to-nodes table children)

mutual
  from-node : List Name → Node → Maybe ConvRecipe
  from-node table (n-list (n-atom 0 ∷ [])) = just c-refl
  from-node table (n-list (n-atom 1 ∷ child ∷ [])) = map c-sym (from-node table child)
  from-node table (n-list (n-atom 2 ∷ middle ∷ left ∷ right ∷ [])) =
    triple c-trans (W.wire-to-term table middle) (from-node table left) (from-node table right)
  from-node table (n-list (n-atom 3 ∷ left ∷ right ∷ [])) =
    pair c-pi (from-node table left) (from-node table right)
  from-node table (n-list (n-atom 4 ∷ left ∷ right ∷ [])) =
    pair c-app (from-node table left) (from-node table right)
  from-node table (n-list (n-atom 5 ∷ n-list ps ∷ n-list is ∷ [])) =
    pair c-data (from-nodes table ps) (from-nodes table is)
  from-node table (n-list (n-atom 6 ∷ n-list children ∷ [])) = map c-ctor (from-nodes table children)
  from-node table (n-list (n-atom 7 ∷ child ∷ [])) = map c-effect-type (from-node table child)
  from-node table (n-list (n-atom 8 ∷ child ∷ [])) = map c-effect-pure (from-node table child)
  from-node table (n-list (n-atom 9 ∷ left ∷ right ∷ [])) =
    pair c-effect-bind (from-node table left) (from-node table right)
  from-node table (n-list (n-atom 10 ∷ [])) = just c-beta
  from-node table (n-list (n-atom 11 ∷ [])) = just c-zeta
  from-node table (n-list (n-atom 12 ∷ n-atom index ∷ [])) = map c-delta (W.lookup-at index table)
  from-node table (n-list (n-atom 13 ∷ [])) = just c-nat-zero
  from-node table (n-list (n-atom 14 ∷ [])) = just c-bounded-zero
  from-node table (n-list (n-atom 15 ∷ [])) = just c-nat-suc
  from-node table (n-list (n-atom 16 ∷ [])) = just c-bounded-suc
  from-node table other = nothing

  from-nodes : List Name → List Node → Maybe (List ConvRecipe)
  from-nodes table [] = just []
  from-nodes table (child ∷ children) = pair _∷_ (from-node table child) (from-nodes table children)

mutual
  fidelity : ∀ table recipe node → to-node table recipe ≡ just node
    → from-node table node ≡ just recipe
  fidelity table c-refl node found with just-inj found
  ... | refl = refl
  fidelity table (c-sym child) node found with to-node table child in encoded
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just body with just-inj found
  ... | refl rewrite fidelity table child body encoded = refl
  fidelity table (c-trans middle left right) node found with W.term-to-wire table middle in encoded-term
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just mid with to-node table left in encoded-left
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just lhs with to-node table right in encoded-right
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just rhs with just-inj found
  ... | refl rewrite W.term-fidelity table middle mid encoded-term
      | fidelity table left lhs encoded-left | fidelity table right rhs encoded-right = refl
  fidelity table (c-pi left right) node found with to-node table left in encoded-left
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just lhs with to-node table right in encoded-right
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just rhs with just-inj found
  ... | refl rewrite fidelity table left lhs encoded-left | fidelity table right rhs encoded-right = refl
  fidelity table (c-app left right) node found with to-node table left in encoded-left
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just lhs with to-node table right in encoded-right
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just rhs with just-inj found
  ... | refl rewrite fidelity table left lhs encoded-left | fidelity table right rhs encoded-right = refl
  fidelity table (c-data ps is) node found with to-nodes table ps in encoded-params
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just params with to-nodes table is in encoded-indices
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just indices with just-inj found
  ... | refl rewrite each-fidelity table ps params encoded-params
      | each-fidelity table is indices encoded-indices = refl
  fidelity table (c-ctor children) node found with to-nodes table children in encoded
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just kids with just-inj found
  ... | refl rewrite each-fidelity table children kids encoded = refl
  fidelity table (c-effect-type child) node found with to-node table child in encoded
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just body with just-inj found
  ... | refl rewrite fidelity table child body encoded = refl
  fidelity table (c-effect-pure child) node found with to-node table child in encoded
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just body with just-inj found
  ... | refl rewrite fidelity table child body encoded = refl
  fidelity table (c-effect-bind left right) node found with to-node table left in encoded-left
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just lhs with to-node table right in encoded-right
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just rhs with just-inj found
  ... | refl rewrite fidelity table left lhs encoded-left | fidelity table right rhs encoded-right = refl
  fidelity table c-beta node found with just-inj found
  ... | refl = refl
  fidelity table c-zeta node found with just-inj found
  ... | refl = refl
  fidelity table (c-delta name) node found with W.index-of name table in indexed
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just index with just-inj found
  ... | refl rewrite W.index-of-sound name table index indexed = refl
  fidelity table c-nat-zero node found with just-inj found
  ... | refl = refl
  fidelity table c-bounded-zero node found with just-inj found
  ... | refl = refl
  fidelity table c-nat-suc node found with just-inj found
  ... | refl = refl
  fidelity table c-bounded-suc node found with just-inj found
  ... | refl = refl

  each-fidelity : ∀ table recipes nodes → to-nodes table recipes ≡ just nodes
    → from-nodes table nodes ≡ just recipes
  each-fidelity table [] nodes found with just-inj found
  ... | refl = refl
  each-fidelity table (child ∷ children) nodes found with to-node table child in encoded-child
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just head with to-nodes table children in encoded-tail
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just tail with just-inj found
  ... | refl rewrite fidelity table child head encoded-child
      | each-fidelity table children tail encoded-tail = refl

encode : List Name → ConvRecipe → Maybe (List Char)
encode table recipe = map W.encode (to-node table recipe)
decode : List Name → List Char → Maybe ConvRecipe
decode table characters with W.decode characters
... | nothing = nothing
... | just node = from-node table node

character-fidelity : ∀ table recipe node → to-node table recipe ≡ just node
  → decode table (W.encode node) ≡ just recipe
character-fidelity table recipe node found
  rewrite W.decode-encode node | fidelity table recipe node found = refl

roundtrip : ∀ table recipe characters → encode table recipe ≡ just characters
  → decode table characters ≡ just recipe
roundtrip table recipe characters found with to-node table recipe in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just node with just-inj found
... | refl = character-fidelity table recipe node encoded

module Replay (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (reduce : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u)
  (owner-visible : ∀ {name family ctor}
    → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
    → findFamily (fam-name family) (IndEnv.families ind) ≡ just family) where
  module D = Core.NativeRecipe.Derive ind sig conv reduce owner-visible

  checked : List Name → (left right : Term) → List Char → Maybe (Conversion._≈_ conv left right)
  checked table left right characters with decode table characters
  ... | nothing = nothing
  ... | just recipe = D.conversion left right recipe
