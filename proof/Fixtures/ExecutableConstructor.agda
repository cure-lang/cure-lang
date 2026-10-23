{-# OPTIONS --guardedness #-}
-- Fixed actual observations, not universal Eval/Quote correspondence.
module Fixtures.ExecutableConstructor where
open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
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
table = "" ∷ "Boundary#Packed" ∷ "Boundary#Pack" ∷ "Boundary#Alternate" ∷ "payload" ∷ "A" ∷ "x" ∷ "Boundary#answer" ∷ "Boundary#held" ∷ "Boundary#packed" ∷ "Boundary#unpack" ∷ "answer" ∷ "hidden" ∷ "First" ∷ []
read-term : (cs : List Char) → present (W.decode-term table cs) ≡ true → Term
read-term cs = pick (W.decode-term table cs)

packed-program : Term
packed-program = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)
packed-environment : List E.Value
packed-environment = []
packed-value : E.Value
packed-value = (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-atom "payload") ∷ []))
packed-quoted : Term
packed-quoted = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)

redex-program : Term
redex-program = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;))(1;;;)))") refl)
redex-environment : List E.Value
redex-environment = []
redex-value : E.Value
redex-value = (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-atom "payload") ∷ []))
redex-quoted : Term
redex-quoted = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)

nested-program : Term
nested-program = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111111;111;;(111111111111111111;;;)(1111111111111111111;1111;;)))") refl)
nested-environment : List E.Value
nested-environment = []
nested-value : E.Value
nested-value = (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-ctor "Boundary#Alternate" (E.v-atom-type ∷ (E.v-atom "payload") ∷ [])) ∷ []))
nested-quoted : Term
nested-quoted = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111111;111;;(111111111111111111;;;)(1111111111111111111;1111;;)))") refl)

field-closure-program : Term
field-closure-program = (read-term (toList "(1111111;11;;(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;;))))") refl)
field-closure-environment : List E.Value
field-closure-environment = []
field-closure-value : E.Value
field-closure-value = (E.v-ctor "Boundary#Pack" ((E.v-lam unrestricted E.v-atom-type [] (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;;))") refl)) ∷ []))
field-closure-quoted : Term
field-closure-quoted = (read-term (toList "(1111111;11;;(111;;111;(111111111111111111;;;)(1;;;)))") refl)

captured-program : Term
captured-program = (read-term (toList "(1111;;111;(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111;;111;(111111111111111111;;;)(1;;1;)))") refl)
captured-environment : List E.Value
captured-environment = []
captured-value : E.Value
captured-value = (E.v-lam unrestricted E.v-atom-type ((E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-atom "payload") ∷ [])) ∷ []) (read-term (toList "(1;;1;)") refl))
captured-quoted : Term
captured-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;)))") refl)

under-binder-program : Term
under-binder-program = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111;11;;(111111111111111111;;;)(1;;;)))") refl)
under-binder-environment : List E.Value
under-binder-environment = []
under-binder-value : E.Value
under-binder-value = (E.v-lam unrestricted E.v-atom-type [] (read-term (toList "(1111111;11;;(111111111111111111;;;)(1;;;))") refl))
under-binder-quoted : Term
under-binder-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111;11;;(111111111111111111;;;)(1;;;)))") refl)

open-program : Term
open-program = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1;;;))") refl)
open-environment : List E.Value
open-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
open-value : E.Value
open-value = (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-neutral (E.n-var 0)) ∷ []))
open-quoted : Term
open-quoted = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1;;;))") refl)

global-field-program : Term
global-field-program = (read-term (toList "(1111111;11;;(111111111111111111;;;)(111111111;1111111;;))") refl)
global-field-environment : List E.Value
global-field-environment = []
global-field-value : E.Value
global-field-value = (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-neutral (E.n-global "Boundary#answer")) ∷ []))
global-field-quoted : Term
global-field-quoted = (read-term (toList "(1111111;11;;(111111111111111111;;;)(111111111;1111111;;))") refl)

case-tree-program : Term
case-tree-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1111111;11;;(111111111111111111;;;)(1111111;111;;(111111111111111111;;;)(1;;;))))))") refl)
case-tree-environment : List E.Value
case-tree-environment = []
case-tree-value : E.Value
case-tree-value = (E.v-ctor "Boundary#Pack" (E.v-atom-type ∷ (E.v-ctor "Boundary#Alternate" (E.v-atom-type ∷ (E.v-atom "payload") ∷ [])) ∷ []))
case-tree-quoted : Term
case-tree-quoted = (read-term (toList "(1111111;11;;(111111111111111111;;;)(1111111;111;;(111111111111111111;;;)(1111111111111111111;1111;;)))") refl)

case-field-program : Term
case-field-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111;111;;(111111111111111111;;;)(1111111111111111111;1111;;)))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;;))))") refl)
case-field-environment : List E.Value
case-field-environment = []
case-field-value : E.Value
case-field-value = (E.v-ctor "Boundary#Alternate" (E.v-atom-type ∷ (E.v-atom "payload") ∷ []))
case-field-quoted : Term
case-field-quoted = (read-term (toList "(1111111;111;;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)

compact-program : Term
compact-program = (read-term (toList "(1111111;1111111111111;;(111111111111111111;;;))") refl)
compact-actual-quoted : Term
compact-actual-quoted = (read-term (toList "(11111111111111;;;)") refl)
data-program : Term
data-program = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))") refl)
data-flat-quoted : Term
data-flat-quoted = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;))(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;))") refl)
data-split-quoted : Term
data-split-quoted = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))") refl)
