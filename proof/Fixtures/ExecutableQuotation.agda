{-# OPTIONS --guardedness #-}
-- Reviewed current Quote observations, not universal implementation refinement.
module Fixtures.ExecutableQuotation where
open import Data.List using (List; []; _∷_)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality using (refl)
open import Core.Syntax using (Term)
open import Core.Grade using (erased; linear; affine; unrestricted)
open import Core.Universe using (l0; l1; l2)
import Core.ClosureEval as E
open import Fixtures.ExecutableClosure using (read-term)

dependent-program : Term
dependent-program = (read-term (toList "(111;;111;(;;;)(111;;111;(1;;;)(11111;;;(111;;111;(1;;1;)(1;;;))(1;;;))))") refl)
dependent-environment : List E.Value
dependent-environment = []
dependent-value : E.Value
dependent-value = (E.v-lam unrestricted (E.v-type l0) [] (read-term (toList "(111;;111;(1;;;)(11111;;;(111;;111;(1;;1;)(1;;;))(1;;;)))") refl))
dependent-quoted : Term
dependent-quoted = (read-term (toList "(111;;111;(;;;)(111;;111;(1;;;)(1;;;)))") refl)
dependent-goal : Term
dependent-goal = (read-term (toList "(11;;111;(;;;)(11;;111;(1;;;)(1;;1;)))") refl)

argument-program : Term
argument-program = (read-term (toList "(11111;;;(1;;;)(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;;))))") refl)
argument-environment : List E.Value
argument-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
argument-value : E.Value
argument-value = (E.v-neutral (E.n-app (E.n-var 0) (E.v-lam unrestricted E.v-atom-type ((E.v-neutral (E.n-var 0)) ∷ []) (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;;))") refl))))
argument-quoted : Term
argument-quoted = (read-term (toList "(11111;;;(1;;;)(111;;111;(111111111111111111;;;)(1;;;)))") refl)
argument-goal : Term
argument-goal = (read-term (toList "(111111111111111111;;;)") refl)

domain-program : Term
domain-program = (read-term (toList "(111;;111;(11;;111;(111111111111111111;;;)(1111;;111;(;;;)(111111111111111111;;;)(1;;;)))(1;;;))") refl)
domain-environment : List E.Value
domain-environment = []
domain-value : E.Value
domain-value = (E.v-lam unrestricted (E.v-pi unrestricted E.v-atom-type [] (read-term (toList "(1111;;111;(;;;)(111111111111111111;;;)(1;;;))") refl)) [] (read-term (toList "(1;;;)") refl))
domain-quoted : Term
domain-quoted = (read-term (toList "(111;;111;(11;;111;(111111111111111111;;;)(111111111111111111;;;))(1;;;))") refl)
domain-goal : Term
domain-goal = (read-term (toList "(11;;111;(11;;111;(111111111111111111;;;)(111111111111111111;;;))(11;;111;(111111111111111111;;;)(111111111111111111;;;)))") refl)

global-program : Term
global-program = (read-term (toList "(111;;111;(111111111111111111;;;)(111111111;1111111;;))") refl)
global-environment : List E.Value
global-environment = []
global-value : E.Value
global-value = (E.v-lam unrestricted E.v-atom-type [] (read-term (toList "(111111111;1111111;;)") refl))
global-quoted : Term
global-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(111111111;1111111;;))") refl)
global-goal : Term
global-goal = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)

eta-program : Term
eta-program = (read-term (toList "(111;;111;(111111111111111111;;;)(11111;;;(1;;1;)(1;;;)))") refl)
eta-environment : List E.Value
eta-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
eta-value : E.Value
eta-value = (E.v-lam unrestricted E.v-atom-type ((E.v-neutral (E.n-var 0)) ∷ []) (read-term (toList "(11111;;;(1;;1;)(1;;;))") refl))
eta-quoted : Term
eta-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(11111;;;(1;;1;)(1;;;)))") refl)
eta-goal : Term
eta-goal = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)

