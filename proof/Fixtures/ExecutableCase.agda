{-# OPTIONS --guardedness #-}
-- Reviewed actual Eval/Quote results, not universal execution refinement.
module Fixtures.ExecutableCase where
open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Term)
open import Core.Grade using (erased; linear; affine; unrestricted)
open import Core.Universe using (l0; l1; l2)
import Core.ClosureEval as E
import Core.Wire as W
import Fixtures.ExecutableBundle as Bundle
open import Proof.CheckedAdmissionExamples using (pick)
open import Core.CheckedAdmission using (present)

read-term : (cs : List Char) → present (W.decode-term Bundle.table cs) ≡ true → Term
read-term cs = pick (W.decode-term Bundle.table cs)

unpack-program : Term
unpack-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111;;111;(;;;)(111;;111;(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(1;;;)))(1;;1;)))(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;;))(;111;11;(1;;;))))") refl)
unpack-environment : List E.Value
unpack-environment = []
unpack-value : E.Value
unpack-value = (E.v-atom "payload")
unpack-quoted : Term
unpack-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

last-program : Term
last-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;;))))") refl)
last-environment : List E.Value
last-environment = []
last-value : E.Value
last-value = (E.v-atom "payload")
last-quoted : Term
last-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

first-program : Term
first-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;1;))))") refl)
first-environment : List E.Value
first-environment = []
first-value : E.Value
first-value = E.v-atom-type
first-quoted : Term
first-quoted = (read-term (toList "(111111111111111111;;;)") refl)

outer-program : Term
outer-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;11;))))") refl)
outer-environment : List E.Value
outer-environment = ((E.v-atom "hidden") ∷ [])
outer-value : E.Value
outer-value = (E.v-atom "hidden")
outer-quoted : Term
outer-quoted = (read-term (toList "(1111111111111111111;111111111111;;)") refl)

nested-program : Term
nested-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;1;))))))") refl)
nested-environment : List E.Value
nested-environment = []
nested-value : E.Value
nested-value = (E.v-lam unrestricted E.v-atom-type ((E.v-atom "payload") ∷ E.v-atom-type ∷ []) (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;1;))") refl))
nested-quoted : Term
nested-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)

nested-outer-program : Term
nested-outer-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;111;))))))") refl)
nested-outer-environment : List E.Value
nested-outer-environment = ((E.v-atom "hidden") ∷ [])
nested-outer-value : E.Value
nested-outer-value = (E.v-lam unrestricted E.v-atom-type ((E.v-atom "payload") ∷ E.v-atom-type ∷ (E.v-atom "hidden") ∷ []) (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;111;))") refl))
nested-outer-quoted : Term
nested-outer-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111111111111111;111111111111;;))") refl)

zero-program : Term
zero-program = (read-term (toList "(11111111;;;(1111111;11;;)(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;;(1111111111111111111;1111;;))))") refl)
zero-environment : List E.Value
zero-environment = []
zero-value : E.Value
zero-value = (E.v-atom "payload")
zero-quoted : Term
zero-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

redex-program : Term
redex-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;)))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1111;;111;(111111111111111111;;;)(1;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;;))))))") refl)
redex-environment : List E.Value
redex-environment = []
redex-value : E.Value
redex-value = (E.v-atom "payload")
redex-quoted : Term
redex-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

duplicate-program : Term
duplicate-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;1;))(;11;11;(1;;;))))") refl)
duplicate-environment : List E.Value
duplicate-environment = []
duplicate-value : E.Value
duplicate-value = E.v-atom-type
duplicate-quoted : Term
duplicate-quoted = (read-term (toList "(111111111111111111;;;)") refl)

skipped-program : Term
skipped-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;111;11;(11111111111111111111;1111;111;))(;11;11;(1;;;))))") refl)
skipped-environment : List E.Value
skipped-environment = []
skipped-value : E.Value
skipped-value = (E.v-atom "payload")
skipped-quoted : Term
skipped-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

inert-motive-program : Term
inert-motive-program = (read-term (toList "(11111111;;;(1111111;11;;(111111111111111111;;;)(1111111111111111111;1111;;))(11111111111111111111;1111;111;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;;))))") refl)
inert-motive-environment : List E.Value
inert-motive-environment = []
inert-motive-value : E.Value
inert-motive-value = (E.v-atom "payload")
inert-motive-quoted : Term
inert-motive-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

filtered-program : Term
filtered-program = (read-term (toList "(11111111;;;(1111111;11;;(1111111111111111111;1111;;)(111111111111111111;;;)(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;;))))") refl)
filtered-environment : List E.Value
filtered-environment = []
filtered-value : E.Value
filtered-value = (E.v-atom "payload")
filtered-quoted : Term
filtered-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

erased-program : Term
erased-program = (read-term (toList "(11111111;;;(1111111;11;;(1111111111111111111;1111;;))(111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(;11;11;(1;;;))))") refl)
erased-environment : List E.Value
erased-environment = []
erased-value : E.Value
erased-value = (E.v-atom "payload")
erased-quoted : Term
erased-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)

