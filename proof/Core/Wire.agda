------------------------------------------------------------------------
-- A SERIALISED WIRE FORMAT for replayed certificate data, with a CHECKED
-- codec. Nothing here trusts the bytes.
--
-- STRUCTURE. A tree is first flattened to a PREFIX-FREE INSTRUCTION
-- stream (`instructions`), and the stream is decoded by a STACK MACHINE
-- (`run`) whose recursion is structural on the stream — no fuel, no
-- well-foundedness side conditions. The instruction stream is then
-- RENDERED to characters (`render`) and the rendering is proved INJECTIVE,
-- so the character string determines the stream, and hence the tree,
-- uniquely.
--
--   instruction  characters            meaning
--   i-atom n     '1'…'1' ';'           leaf holding the natural n
--   i-open       '('                   open a child list
--   i-close      ')'                   close the current child list
--
-- Natural payloads are unary so the round-trip needs no arithmetic
-- lemmas; a compact decimal or JSON layer is a purely syntactic
-- refinement and carries no soundness obligation.
--
-- NAMES ARE INTERNED. A character-faithful round-trip for `String` is NOT
-- available here: the standard library only offers injectivity of
-- `primStringToList`/`primStringFromList`, and the missing round-trip
-- (`fromList∘toList`) exists only as a postulate in `Data.String.Unsafe`,
-- which this development does not use. The wire therefore carries a name
-- TABLE INDEX, exactly as the canonical snapshot resolves owner-qualified
-- keys against its registry: encoding is partial (a name absent from the
-- table cannot be written) and decoding looks the index up.
--
-- BOUNDARY. This module fixes the format and decodes INSTRUCTION STREAMS.
-- An executable character-level parser is the remaining syntactic step
-- (it needs a termination argument of its own); character-level
-- UNAMBIGUITY — the property a decoder must preserve — is proved here.
------------------------------------------------------------------------
module Core.Wire where

open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (length-++)
open import Data.Nat using (pred)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Core.Syntax using (Name)
open import Core.Signature using (just-inj; nothing≠just)
import Data.String.Properties as String

------------------------------------------------------------------------
-- Alphabet
------------------------------------------------------------------------

one : Char
one = '1'

stop : Char
stop = ';'

open-paren close-paren : Char
open-paren = '('
close-paren = ')'

one≠stop : one ≢ stop
one≠stop = λ ()

one≠open : one ≢ open-paren
one≠open = λ ()

one≠close : one ≢ close-paren
one≠close = λ ()

stop≠open : stop ≢ open-paren
stop≠open = λ ()

stop≠close : stop ≢ close-paren
stop≠close = λ ()

open≠close : open-paren ≢ close-paren
open≠close = λ ()

------------------------------------------------------------------------
-- Trees and their instruction streams
------------------------------------------------------------------------

data Node : Set where
  n-atom : ℕ → Node
  n-list : List Node → Node

data Instr : Set where
  i-atom : ℕ → Instr
  i-open : Instr
  i-close : Instr

instructions : Node → List Instr
instructions-items : List Node → List Instr
instructions (n-atom k) = i-atom k ∷ []
instructions (n-list nodes) = i-open ∷ instructions-items nodes ++ (i-close ∷ [])
instructions-items [] = []
instructions-items (node ∷ nodes) = instructions node ++ instructions-items nodes

------------------------------------------------------------------------
-- The decoding machine
--
-- The stack holds one CHILD ACCUMULATOR per open list, most recent first.
-- Children are accumulated in WRITE order and a list closes when its
-- `i-close` arrives, so no reversal is needed.
------------------------------------------------------------------------

machine : List (List Node) → List Instr → Maybe Node
machine-after : Node → List (List Node) → List Instr → Maybe Node

machine [] [] = nothing
machine [] (i-atom k ∷ is) = machine-after (n-atom k) [] is
machine [] (i-open ∷ is) = machine ([] ∷ []) is
machine [] (i-close ∷ is) = nothing
machine (acc ∷ frames) (i-atom k ∷ is) = machine-after (n-atom k) (acc ∷ frames) is
machine (acc ∷ frames) (i-open ∷ is) = machine ([] ∷ acc ∷ frames) is
machine (acc ∷ frames) (i-close ∷ is) = machine-after (n-list acc) frames is
machine (acc ∷ frames) [] = nothing

machine-after node [] [] = just node
machine-after node [] (i ∷ is) = nothing
machine-after node (acc ∷ frames) is = machine ((acc ++ (node ∷ [])) ∷ frames) is

run : List Instr → Maybe Node
run = machine []

-- Reading the children of one list: the accumulator grows by exactly the
-- child list, and the list is closed and delivered to the parent.
items-lemma : ∀ nodes acc frames is
  → machine (acc ∷ frames) (instructions-items nodes ++ (i-close ∷ is))
  ≡ machine-after (n-list (acc ++ nodes)) frames is
-- Reading one node into the innermost open list.
node-lemma : ∀ node acc frames is
  → machine (acc ∷ frames) (instructions node ++ is)
  ≡ machine-after node (acc ∷ frames) is

run-instructions : ∀ node → run (instructions node) ≡ just node
run-instructions (n-atom k) = refl
run-instructions (n-list nodes) = items-lemma nodes [] [] []

items-lemma [] acc frames is =
  cong (λ acc′ → machine-after (n-list acc′) frames is) (sym (++-identityʳ acc))
items-lemma (node ∷ nodes) acc frames is =
  trans (cong (λ rest → machine (acc ∷ frames) rest)
      (++-assoc (instructions node) (instructions-items nodes) (i-close ∷ is)))
    (trans (node-lemma node acc frames (instructions-items nodes ++ (i-close ∷ is)))
    (trans (items-lemma nodes (acc ++ (node ∷ [])) frames is)
      (cong (λ acc′ → machine-after (n-list acc′) frames is)
        (++-assoc acc (node ∷ []) nodes))))

node-lemma (n-atom k) acc frames is = refl
node-lemma (n-list nodes) acc frames is =
  trans (cong (λ rest → machine ([] ∷ acc ∷ frames) rest)
      (++-assoc (instructions-items nodes) (i-close ∷ []) is))
    (trans (items-lemma nodes [] (acc ∷ frames) is)
      (cong (λ ns → machine-after (n-list ns) (acc ∷ frames) is)
        (++-identityˡ nodes)))

------------------------------------------------------------------------
-- Rendering to characters, proved UNAMBIGUOUS
------------------------------------------------------------------------

unary : ℕ → List Char
unary zero = []
unary (suc n) = one ∷ unary n

render : Instr → List Char
render (i-atom k) = unary k ++ (stop ∷ [])
render i-open = open-paren ∷ []
render i-close = close-paren ∷ []

render-items : List Instr → List Char
render-items [] = []
render-items (i ∷ is) = render i ++ render-items is

unary-length : ∀ n → length (unary n) ≡ n
unary-length zero = refl
unary-length (suc n) = cong suc (unary-length n)

unary-rendering-length : ∀ n → length (unary n ++ stop ∷ []) ≡ suc n
unary-rendering-length n =
  trans (length-++ (unary n))
    (trans (cong (λ m → m + length (stop ∷ [])) (unary-length n))
      (trans (+-suc n zero) (cong suc (+-identityʳ n))))

-- Unary runs are prefix-free on their own: equal renderings imply equal
-- lengths (the terminator makes the two runs the same length).
unary-injective : ∀ m n → unary m ++ stop ∷ [] ≡ unary n ++ stop ∷ [] → m ≡ n
unary-injective m n eq =
  cong pred (trans (sym (unary-rendering-length m))
    (trans (cong length eq) (unary-rendering-length n)))

-- The first character of an instruction's rendering, and the rest.
first : Instr → Char
first (i-atom zero) = stop
first (i-atom (suc k)) = one
first i-open = open-paren
first i-close = close-paren

FirstOf : Instr → Set
FirstOf i = Σ (List Char) (λ rest → render i ≡ first i ∷ rest)

head-of : ∀ i → FirstOf i
head-of (i-atom zero) = [] , refl
head-of (i-atom (suc k)) = unary k ++ (stop ∷ []) , refl
head-of i-open = [] , refl
head-of i-close = [] , refl

head-eq : ∀ {x y : Char} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
head-eq refl = refl

first-eq : ∀ i j → render i ≡ render j → first i ≡ first j
first-eq i j eq =
  head-eq (trans (sym (proj₂ (head-of i))) (trans eq (proj₂ (head-of j))))

-- A single instruction's rendering determines the instruction, so the
-- characters carry the instruction stream without ambiguity.
render-injective : ∀ i j → render i ≡ render j → i ≡ j
render-injective (i-atom m) (i-atom n) eq = cong i-atom (unary-injective m n eq)
render-injective (i-atom zero) i-open eq =
  ⊥-elim (stop≠open (first-eq (i-atom zero) i-open eq))
render-injective (i-atom zero) i-close eq =
  ⊥-elim (stop≠close (first-eq (i-atom zero) i-close eq))
render-injective (i-atom (suc m)) i-open eq =
  ⊥-elim (one≠open (first-eq (i-atom (suc m)) i-open eq))
render-injective (i-atom (suc m)) i-close eq =
  ⊥-elim (one≠close (first-eq (i-atom (suc m)) i-close eq))
render-injective i-open (i-atom zero) eq =
  ⊥-elim (stop≠open (sym (first-eq i-open (i-atom zero) eq)))
render-injective i-open (i-atom (suc n)) eq =
  ⊥-elim (one≠open (sym (first-eq i-open (i-atom (suc n)) eq)))
render-injective i-open i-close eq = ⊥-elim (open≠close (first-eq i-open i-close eq))
render-injective i-close (i-atom zero) eq =
  ⊥-elim (stop≠close (sym (first-eq i-close (i-atom zero) eq)))
render-injective i-close (i-atom (suc n)) eq =
  ⊥-elim (one≠close (sym (first-eq i-close (i-atom (suc n)) eq)))
render-injective i-close i-open eq =
  ⊥-elim (open≠close (sym (first-eq i-close i-open eq)))
render-injective i-open i-open eq = refl
render-injective i-close i-close eq = refl

------------------------------------------------------------------------
-- Name interning
------------------------------------------------------------------------

index-of : (name : Name) (table : List Name) → Maybe ℕ
index-of name [] = nothing
index-of name (x ∷ table) with name String.≟ x
... | yes same = just zero
... | no different with index-of name table
...   | nothing = nothing
...   | just i = just (suc i)

lookup-at : ℕ → List Name → Maybe Name
lookup-at zero [] = nothing
lookup-at zero (x ∷ table) = just x
lookup-at (suc i) [] = nothing
lookup-at (suc i) (x ∷ table) = lookup-at i table

-- An index produced by `index-of` really points at that name, so an
-- interned wire payload decodes to the name that was written.

index-of-sound : ∀ name table i
  → index-of name table ≡ just i → lookup-at i table ≡ just name
index-of-sound name [] i ()
index-of-sound name (x ∷ table) i found with name String.≟ x
... | yes refl =
  subst (λ index → lookup-at index (x ∷ table) ≡ just name)
    (just-inj found) refl
... | no different with index-of name table in nested
...   | nothing = ⊥-elim (nothing≠just found)
...   | just j = subst (λ index → lookup-at index (x ∷ table) ≡ just name)
      (just-inj found) (index-of-sound name table j nested)
