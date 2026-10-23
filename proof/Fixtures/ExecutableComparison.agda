{-# OPTIONS --guardedness #-}
-- Reviewed actual Conv/Quote observations; not universal conversion refinement.
module Fixtures.ExecutableComparison where
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality using (refl)
open import Core.Syntax using (Term)
import Core.ClosureEval as E
open import Fixtures.ExecutableClosure using (read-term)

beta-left beta-right beta-left-quoted beta-right-quoted : Term
beta-left = (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;))") refl)
beta-right = (read-term (toList "(1111111111111111111;1111;;)") refl)
beta-left-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
beta-right-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
beta-environment : List E.Value
beta-environment = []
beta-depth : ℕ
beta-depth = 0
beta-actual beta-quoted-equal beta-with-signature : Bool
beta-actual = true
beta-quoted-equal = true
beta-with-signature = false

zeta-left zeta-right zeta-left-quoted zeta-right-quoted : Term
zeta-left = (read-term (toList "(1111;;111;(111111111111111111;;;)(1111111111111111111;1111;;)(1;;;))") refl)
zeta-right = (read-term (toList "(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1111111111111111111;1111;;))") refl)
zeta-left-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
zeta-right-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
zeta-environment : List E.Value
zeta-environment = []
zeta-depth : ℕ
zeta-depth = 0
zeta-actual zeta-quoted-equal zeta-with-signature : Bool
zeta-actual = true
zeta-quoted-equal = true
zeta-with-signature = false

lambda-left lambda-right lambda-left-quoted lambda-right-quoted : Term
lambda-left = (read-term (toList "(111;;111;(111111111111111111;;;)(11111;;;(111;;111;(111111111111111111;;;)(1;;;))(1;;;)))") refl)
lambda-right = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;;))") refl)
lambda-left-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;;))") refl)
lambda-right-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;;))") refl)
lambda-environment : List E.Value
lambda-environment = []
lambda-depth : ℕ
lambda-depth = 0
lambda-actual lambda-quoted-equal lambda-with-signature : Bool
lambda-actual = true
lambda-quoted-equal = true
lambda-with-signature = false

pi-left pi-right pi-left-quoted pi-right-quoted : Term
pi-left = (read-term (toList "(11;;111;(111111111111111111;;;)(11111;;;(111;;111;(;;;)(1;;;))(111111111111111111;;;)))") refl)
pi-right = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-left-quoted = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-right-quoted = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-environment : List E.Value
pi-environment = []
pi-depth : ℕ
pi-depth = 0
pi-actual pi-quoted-equal pi-with-signature : Bool
pi-actual = true
pi-quoted-equal = true
pi-with-signature = false

lambda-grade-left lambda-grade-right lambda-grade-left-quoted lambda-grade-right-quoted : Term
lambda-grade-left = (read-term (toList "(111;;1;(111111111111111111;;;)(1;;;))") refl)
lambda-grade-right = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;;))") refl)
lambda-grade-left-quoted = (read-term (toList "(111;;1;(111111111111111111;;;)(1;;;))") refl)
lambda-grade-right-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1;;;))") refl)
lambda-grade-environment : List E.Value
lambda-grade-environment = []
lambda-grade-depth : ℕ
lambda-grade-depth = 0
lambda-grade-actual lambda-grade-quoted-equal lambda-grade-with-signature : Bool
lambda-grade-actual = false
lambda-grade-quoted-equal = false
lambda-grade-with-signature = false

pi-grade-left pi-grade-right pi-grade-left-quoted pi-grade-right-quoted : Term
pi-grade-left = (read-term (toList "(11;;1;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-grade-right = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-grade-left-quoted = (read-term (toList "(11;;1;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-grade-right-quoted = (read-term (toList "(11;;111;(111111111111111111;;;)(111111111111111111;;;))") refl)
pi-grade-environment : List E.Value
pi-grade-environment = []
pi-grade-depth : ℕ
pi-grade-depth = 0
pi-grade-actual pi-grade-quoted-equal pi-grade-with-signature : Bool
pi-grade-actual = false
pi-grade-quoted-equal = false
pi-grade-with-signature = false

universe-left universe-right universe-left-quoted universe-right-quoted : Term
universe-left = (read-term (toList "(;;;)") refl)
universe-right = (read-term (toList "(;;1;)") refl)
universe-left-quoted = (read-term (toList "(;;;)") refl)
universe-right-quoted = (read-term (toList "(;;1;)") refl)
universe-environment : List E.Value
universe-environment = []
universe-depth : ℕ
universe-depth = 0
universe-actual universe-quoted-equal universe-with-signature : Bool
universe-actual = false
universe-quoted-equal = false
universe-with-signature = false

name-left name-right name-left-quoted name-right-quoted : Term
name-left = (read-term (toList "(1111111111111111111;1111;;)") refl)
name-right = (read-term (toList "(1111111111111111111;111111111111;;)") refl)
name-left-quoted = (read-term (toList "(1111111111111111111;1111;;)") refl)
name-right-quoted = (read-term (toList "(1111111111111111111;111111111111;;)") refl)
name-environment : List E.Value
name-environment = []
name-depth : ℕ
name-depth = 0
name-actual name-quoted-equal name-with-signature : Bool
name-actual = false
name-quoted-equal = false
name-with-signature = false

eta-left eta-right eta-left-quoted eta-right-quoted : Term
eta-left = (read-term (toList "(111;;111;(111111111111111111;;;)(11111;;;(1;;1;)(1;;;)))") refl)
eta-right = (read-term (toList "(1;;;)") refl)
eta-left-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(11111;;;(1;;1;)(1;;;)))") refl)
eta-right-quoted = (read-term (toList "(1;;;)") refl)
eta-environment : List E.Value
eta-environment = ((E.v-neutral (E.n-var 0)) ∷ [])
eta-depth : ℕ
eta-depth = 1
eta-actual eta-quoted-equal eta-with-signature : Bool
eta-actual = true
eta-quoted-equal = false
eta-with-signature = false

domain-left domain-right domain-left-quoted domain-right-quoted : Term
domain-left = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)
domain-right = (read-term (toList "(111;;111;(;;;)(1111111111111111111;1111;;))") refl)
domain-left-quoted = (read-term (toList "(111;;111;(111111111111111111;;;)(1111111111111111111;1111;;))") refl)
domain-right-quoted = (read-term (toList "(111;;111;(;;;)(1111111111111111111;1111;;))") refl)
domain-environment : List E.Value
domain-environment = []
domain-depth : ℕ
domain-depth = 0
domain-actual domain-quoted-equal domain-with-signature : Bool
domain-actual = true
domain-quoted-equal = false
domain-with-signature = false

delta-left delta-right delta-left-quoted delta-right-quoted : Term
delta-left = (read-term (toList "(111111111;1111111;;)") refl)
delta-right = (read-term (toList "(1111111111111111111;11111111111;;)") refl)
delta-left-quoted = (read-term (toList "(111111111;1111111;;)") refl)
delta-right-quoted = (read-term (toList "(1111111111111111111;11111111111;;)") refl)
delta-environment : List E.Value
delta-environment = []
delta-depth : ℕ
delta-depth = 0
delta-actual delta-quoted-equal delta-with-signature : Bool
delta-actual = true
delta-quoted-equal = false
delta-with-signature = true

data-left data-right data-left-quoted data-right-quoted : Term
data-left = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))") refl)
data-right = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))") refl)
data-left-quoted = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))") refl)
data-right-quoted = (read-term (toList "(111111;1;;(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;)(1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111;;;(111111111111111111;;;)))") refl)
data-environment : List E.Value
data-environment = []
data-depth : ℕ
data-depth = 0
data-actual data-quoted-equal data-with-signature : Bool
data-actual = true
data-quoted-equal = true
data-with-signature = true

