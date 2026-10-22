{-# OPTIONS --guardedness #-}
-- Reviewed actual Eval/Quote observations, not universal execution refinement.
module Fixtures.ExecutableClosure where
open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
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

beta-program : Term
beta-program = (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;))") refl)
beta-environment : List E.Value
beta-environment = []
beta-value : E.Value
beta-value = (E.v-atom "payload")
beta-quoted : Term
beta-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
beta-goal : Term
beta-goal = (read-term (toList "(111111111111111111;;;)") refl)

argument-program : Term
argument-program = (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;)))") refl)
argument-environment : List E.Value
argument-environment = []
argument-value : E.Value
argument-value = (E.v-atom "payload")
argument-quoted : Term
argument-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
argument-goal : Term
argument-goal = (read-term (toList "(111111111111111111;;;)") refl)

capture-program : Term
capture-program = (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;1;))))(1111111111111111111;1111;;))") refl)
capture-environment : List E.Value
capture-environment = []
capture-value : E.Value
capture-value = (E.v-lam unrestricted E.v-atom-type ((E.v-atom "payload") ∷ []) (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;1;))") refl))
capture-quoted : Term
capture-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)
capture-goal : Term
capture-goal = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)

higher-program : Term
higher-program = (read-term (toList "(11111;;;(111;;111;(11;;111;(111111111111111111;;;)(111111111111111111;;;))(11111;;;(1;;;)(1111111111111111111;1111;;)))(111;;111;(111111111111111111;;;)(1;;;)))") refl)
higher-environment : List E.Value
higher-environment = []
higher-value : E.Value
higher-value = (E.v-atom "payload")
higher-quoted : Term
higher-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
higher-goal : Term
higher-goal = (read-term (toList "(111111111111111111;;;)") refl)

let-program : Term
let-program = (read-term (toList "(1111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;))(1;;;))") refl)
let-environment : List E.Value
let-environment = []
let-value : E.Value
let-value = (E.v-atom "payload")
let-quoted : Term
let-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
let-goal : Term
let-goal = (read-term (toList "(111111111111111111;;;)") refl)

domain-program : Term
domain-program = (read-term (toList "(111;;111;(1111;;111;(;;;)(111111111111111111;;;)(1;;;))(1;;;))") refl)
domain-environment : List E.Value
domain-environment = []
domain-value : E.Value
domain-value = (E.v-lam unrestricted E.v-atom-type [] (read-term (toList "(1;;;)") refl))
domain-quoted : Term
domain-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;;))") refl)
domain-goal : Term
domain-goal = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)

annotation-program : Term
annotation-program = (read-term (toList "(1111;;111;(11111111111111111111;1111;111;)(1111111111111111111;1111;;)(1;;;))") refl)
annotation-environment : List E.Value
annotation-environment = []
annotation-value : E.Value
annotation-value = (E.v-atom "payload")
annotation-quoted : Term
annotation-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
annotation-goal : Term
annotation-goal = (read-term (toList "(111111111111111111;;;)") refl)

neutral-program : Term
neutral-program = (read-term (toList "(11111;;;(1;;;)(1111111111111111111;1111;;))") refl)
neutral-environment : List E.Value
neutral-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
neutral-value : E.Value
neutral-value = (E.v-neutral (E.n-app (E.n-var 0) (E.v-atom "payload")))
neutral-quoted : Term
neutral-quoted = (read-term (toList "(11111;;;(1;;;)(1111111111111111111;1111;;))") refl)
neutral-goal : Term
neutral-goal = (read-term (toList "(111111111111111111;;;)") refl)

global-program : Term
global-program = (read-term (toList "(111111111;1111111;;)") refl)
global-environment : List E.Value
global-environment = []
global-value : E.Value
global-value = (E.v-neutral (E.n-global "Boundary#answer"))
global-quoted : Term
global-quoted = (read-term (toList "(111111111;1111111;;)") refl)
global-goal : Term
global-goal = (read-term (toList "(111111111111111111;;;)") refl)

pi-program : Term
pi-program = (read-term (toList "(11;;111;(1111;;111;(;;;)(111111111111111111;;;)(1;;;))(111111111111111111;;;))") refl)
pi-environment : List E.Value
pi-environment = []
pi-value : E.Value
pi-value = (E.v-pi unrestricted E.v-atom-type [] (read-term (toList "(111111111111111111;;;)") refl))
pi-quoted : Term
pi-quoted = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-goal : Term
pi-goal = (read-term (toList "(;;;)") refl)

