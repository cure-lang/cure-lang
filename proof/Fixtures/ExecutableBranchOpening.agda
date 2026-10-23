{-# OPTIONS --guardedness #-}
-- Fixed actual Eval.open_branch/Quote observations, not universal refinement.
module Fixtures.ExecutableBranchOpening where
open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Name; Term)
open import Core.Grade using (erased; linear; affine; unrestricted)
open import Core.Universe using (l0; l1; l2)
import Core.ClosureEval as E
import Core.Wire as W
open import Proof.CheckedAdmissionExamples using (pick)
open import Core.CheckedAdmission using (present)
table : List Name
table = "" ∷ "Spine#Indexed" ∷ "Spine#Unknown" ∷ "A" ∷ "x" ∷ "payload" ∷ "Opening#Frame" ∷ []
read-term : (cs : List Char) → present (W.decode-term table cs) ≡ true → Term
read-term cs = pick (W.decode-term table cs)
zero-depth : ℕ
zero-depth = 0
zero-arity : ℕ
zero-arity = 0
zero-environment : List E.Value
zero-environment = ((E.v-atom "payload") ∷ [])
zero-opened : List E.Value
zero-opened = ((E.v-atom "payload") ∷ [])
zero-body : Term
zero-body = (read-term (toList "(1;;;)") refl)
zero-value : E.Value
zero-value = (E.v-atom "payload")
zero-quoted : Term
zero-quoted = (read-term (toList "(1111111111111111111;11111;;)") refl)

one-depth : ℕ
one-depth = 0
one-arity : ℕ
one-arity = 1
one-environment : List E.Value
one-environment = []
one-opened : List E.Value
one-opened = ((E.v-neutral (E.n-var 0)) ∷ [])
one-body : Term
one-body = (read-term (toList "(1;;;)") refl)
one-value : E.Value
one-value = (E.v-neutral (E.n-var 0))
one-quoted : Term
one-quoted = (read-term (toList "(1;;;)") refl)

first-depth : ℕ
first-depth = 1
first-arity : ℕ
first-arity = 3
first-environment : List E.Value
first-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
first-opened : List E.Value
first-opened = ((E.v-neutral (E.n-var 3)) ∷ (E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
first-body : Term
first-body = (read-term (toList "(1;;11;)") refl)
first-value : E.Value
first-value = (E.v-neutral (E.n-var 1))
first-quoted : Term
first-quoted = (read-term (toList "(1;;11;)") refl)

last-depth : ℕ
last-depth = 1
last-arity : ℕ
last-arity = 3
last-environment : List E.Value
last-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
last-opened : List E.Value
last-opened = ((E.v-neutral (E.n-var 3)) ∷ (E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
last-body : Term
last-body = (read-term (toList "(1;;;)") refl)
last-value : E.Value
last-value = (E.v-neutral (E.n-var 3))
last-quoted : Term
last-quoted = (read-term (toList "(1;;;)") refl)

outer-depth : ℕ
outer-depth = 1
outer-arity : ℕ
outer-arity = 3
outer-environment : List E.Value
outer-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
outer-opened : List E.Value
outer-opened = ((E.v-neutral (E.n-var 3)) ∷ (E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
outer-body : Term
outer-body = (read-term (toList "(1;;111;)") refl)
outer-value : E.Value
outer-value = (E.v-neutral (E.n-var 0))
outer-quoted : Term
outer-quoted = (read-term (toList "(1;;111;)") refl)

closure-depth : ℕ
closure-depth = 0
closure-arity : ℕ
closure-arity = 2
closure-environment : List E.Value
closure-environment = ((E.v-atom "payload") ∷ [])
closure-opened : List E.Value
closure-opened = ((E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ (E.v-atom "payload") ∷ [])
closure-body : Term
closure-body = (read-term (toList "(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;111;)))") refl)
closure-value : E.Value
closure-value = (E.v-lam unrestricted E.v-atom-type ((E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ (E.v-atom "payload") ∷ []) (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;111;))") refl))
closure-quoted : Term
closure-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111111111111111;11111;;))") refl)

spine-depth : ℕ
spine-depth = 1
spine-arity : ℕ
spine-arity = 2
spine-environment : List E.Value
spine-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
spine-opened : List E.Value
spine-opened = ((E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
spine-body : Term
spine-body = (read-term (toList "(1111111;111111;;(1;;1;)(1;;;)(1;;11;))") refl)
spine-value : E.Value
spine-value = (E.v-ctor "Opening#Frame" ((E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 0)) ∷ []))
spine-quoted : Term
spine-quoted = (read-term (toList "(1111111;111111;;(1;;1;)(1;;;)(1;;11;))") refl)

redex-depth : ℕ
redex-depth = 0
redex-arity : ℕ
redex-arity = 2
redex-environment : List E.Value
redex-environment = []
redex-opened : List E.Value
redex-opened = ((E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
redex-body : Term
redex-body = (read-term (toList "(1111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;1;))(1;;;))") refl)
redex-value : E.Value
redex-value = (E.v-neutral (E.n-var 0))
redex-quoted : Term
redex-quoted = (read-term (toList "(1;;1;)") refl)

data-depth : ℕ
data-depth = 1
data-arity : ℕ
data-arity = 2
data-environment : List E.Value
data-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
data-opened : List E.Value
data-opened = ((E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
data-body : Term
data-body = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;))(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(1;;1;)))") refl)
data-value : E.Value
data-value = (E.v-data "Spine#Indexed" (E.v-atom-type ∷ []) ((E.v-neutral (E.n-var 1)) ∷ []))
data-quoted : Term
data-quoted = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;))(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(1;;1;)))") refl)

capture-depth : ℕ
capture-depth = 0
capture-arity : ℕ
capture-arity = 1
capture-environment : List E.Value
capture-environment = ((E.v-data "Spine#Indexed" (E.v-atom-type ∷ []) ((E.v-atom "payload") ∷ [])) ∷ [])
capture-opened : List E.Value
capture-opened = ((E.v-neutral (E.n-var 0)) ∷ (E.v-data "Spine#Indexed" (E.v-atom-type ∷ []) ((E.v-atom "payload") ∷ [])) ∷ [])
capture-body : Term
capture-body = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;11;))") refl)
capture-value : E.Value
capture-value = (E.v-lam unrestricted E.v-atom-type ((E.v-neutral (E.n-var 0)) ∷ (E.v-data "Spine#Indexed" (E.v-atom-type ∷ []) ((E.v-atom "payload") ∷ [])) ∷ []) (read-term (toList "(1;;11;)") refl))
capture-quoted : Term
capture-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;))(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(1111111111111111111;11111;;))))") refl)

case-depth : ℕ
case-depth = 1
case-arity : ℕ
case-arity = 2
case-environment : List E.Value
case-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
case-opened : List E.Value
case-opened = ((E.v-neutral (E.n-var 2)) ∷ (E.v-neutral (E.n-var 1)) ∷ (E.v-neutral (E.n-var 0)) ∷ [])
case-body : Term
case-body = (read-term (toList "(11111111;;;(1111111;111111;;(1;;1;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;111111;1;(1;;;))))") refl)
case-value : E.Value
case-value = (E.v-neutral (E.n-var 1))
case-quoted : Term
case-quoted = (read-term (toList "(1;;1;)") refl)

