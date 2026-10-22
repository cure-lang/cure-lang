------------------------------------------------------------------------
-- Nonrecursive container combinators. Every read checks its exact shape;
-- faithful record transport needs only a proved project/build retraction.
------------------------------------------------------------------------
module Core.WireCombinators where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Signature using (nothing≠just; just-inj)
open import Core.Wire using (Node; n-atom; n-list)
open import Core.WireCertificate using (Codec; module Vector)
open Codec
import Core.WireConversion as C

bind : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bind nothing next = nothing
bind (just value) next = next value

product-read : ∀ {A B} → Codec A → Codec B → Node → Maybe (A × B)
product-read a b (n-list (left ∷ right ∷ [])) = C.pair _,_ (read a left) (read b right)
product-read a b other = nothing
product-fidelity : ∀ {A B} (a : Codec A) (b : Codec B) x y node
  → C.pair (λ l r → n-list (l ∷ r ∷ [])) (write a x) (write b y) ≡ just node
  → product-read a b node ≡ just (x , y)
product-fidelity a b x y node found with write a x in ex
... | nothing = ⊥-elim (nothing≠just found)
... | just nx with write b y in ey
... | nothing = ⊥-elim (nothing≠just found)
... | just ny with just-inj found
... | refl rewrite faithful a x nx ex | faithful b y ny ey = refl
both : ∀ {A B} → Codec A → Codec B → Codec (A × B)
both a b = record
  { write = λ { (x , y) → C.pair (λ l r → n-list (l ∷ r ∷ [])) (write a x) (write b y) }
  ; read = product-read a b
  ; faithful = λ { (x , y) → product-fidelity a b x y } }

list-read : ∀ {A} → Codec A → Node → Maybe (List A)
list-read codec (n-list ns) = Vector.read-list codec ns
list-read codec other = nothing
list-fidelity : ∀ {A} (codec : Codec A) values node
  → C.map n-list (Vector.write-list codec values) ≡ just node
  → list-read codec node ≡ just values
list-fidelity codec values node found with Vector.write-list codec values in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just ns with just-inj found
... | refl = Vector.list-fidelity codec values ns encoded
many : ∀ {A} → Codec A → Codec (List A)
many codec = record
  { write = λ values → C.map n-list (Vector.write-list codec values)
  ; read = list-read codec ; faithful = list-fidelity codec }

optional-write : ∀ {A} → Codec A → Maybe A → Maybe Node
optional-write codec nothing = just (n-list [])
optional-write codec (just value) = C.map (λ n → n-list (n ∷ [])) (write codec value)
optional-read : ∀ {A} → Codec A → Node → Maybe (Maybe A)
optional-read codec (n-list []) = just nothing
optional-read codec (n-list (node ∷ [])) = C.map just (read codec node)
optional-read codec other = nothing
optional-fidelity : ∀ {A} (codec : Codec A) value node
  → optional-write codec value ≡ just node → optional-read codec node ≡ just value
optional-fidelity codec nothing node found with just-inj found
... | refl = refl
optional-fidelity codec (just value) node found with write codec value in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just n with just-inj found
... | refl rewrite faithful codec value n encoded = refl
optional : ∀ {A} → Codec A → Codec (Maybe A)
optional codec = record
  { write = optional-write codec ; read = optional-read codec ; faithful = optional-fidelity codec }

untag : ℕ → Node → Maybe Node
untag tag (n-list (n-atom actual ∷ body ∷ [])) with Nat._≟_ actual tag
... | yes same = just body
... | no different = nothing
untag tag other = nothing
untag-fidelity : ∀ tag node → untag tag (C.tagged tag (node ∷ [])) ≡ just node
untag-fidelity tag node with Nat._≟_ tag tag
... | yes same = refl
... | no different = ⊥-elim (different refl)
tag-fidelity : ∀ {A} tag (codec : Codec A) value node
  → C.map (λ n → C.tagged tag (n ∷ [])) (write codec value) ≡ just node
  → bind (untag tag node) (read codec) ≡ just value
tag-fidelity tag codec value node found with write codec value in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just n with just-inj found
... | refl rewrite untag-fidelity tag n = faithful codec value n encoded
tagged : ∀ {A} → ℕ → Codec A → Codec A
tagged tag codec = record
  { write = λ value → C.map (λ n → C.tagged tag (n ∷ [])) (write codec value)
  ; read = λ node → bind (untag tag node) (read codec)
  ; faithful = tag-fidelity tag codec }

record-read : ∀ {A B : Set} → Codec A → (A → B) → Node → Maybe B
record-read codec build node = C.map build (read codec node)
record-fidelity : ∀ {A B : Set} (codec : Codec A) (build : A → B) (project : B → A)
  → (∀ value → build (project value) ≡ value)
  → ∀ value node → write codec (project value) ≡ just node
  → record-read codec build node ≡ just value
record-fidelity codec build project retract value node found
  rewrite faithful codec (project value) node found | retract value = refl
iso : ∀ {A B : Set} → Codec A → (build : A → B) → (project : B → A)
  → (∀ value → build (project value) ≡ value) → Codec B
iso codec build project retract = record
  { write = λ value → write codec (project value)
  ; read = record-read codec build ; faithful = record-fidelity codec build project retract }
