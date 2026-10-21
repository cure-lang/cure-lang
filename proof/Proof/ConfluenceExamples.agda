------------------------------------------------------------------------
-- Concrete witnesses for checked SPECIFICATION confluence, independently
-- of typing or conversion. Field zero is the LAST exact-arity field.
-- Parameter filtering and missing erased slots remain separate repairs.
------------------------------------------------------------------------
module Proof.ConfluenceExamples where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; _×_; _,_)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (unrestricted)
open import Core.Syntax
open import Core.Reduction
open import Core.Relation
open import Core.StrictParallel
open import Proof.Confluence using (ClosedBody; module Conf)
import Proof.LiteralCases as L

module N = Parallel L.empty-sig
module C = L.Confluent

seven nine : Term
seven = tm-int_lit (pos 7)
nine = tm-int_lit (pos 9)

wrap : Term → Term
wrap t = tm-let unrestricted tm-int_type t (tm-var 0)

-- A beta peak whose body and argument both reduce concurrently.
lambda-body : Term
lambda-body = wrap (tm-var 0)

argument : Term
argument = wrap seven

beta-peak : Term
beta-peak = tm-app (tm-lam unrestricted tm-int_type lambda-body) argument

beta-left beta-right : Term
beta-left = wrap argument
beta-right = tm-app (tm-lam unrestricted tm-int_type (tm-var 0)) seven

beta-root : N._⇛_ beta-peak beta-left
beta-root = N.s-beta (N.reflexive _) (N.reflexive _) (N.reflexive _)

beta-congruence : N._⇛_ beta-peak beta-right
beta-congruence =
  N.s-app (N.s-lam (N.reflexive _)
    (N.s-zeta (N.reflexive _) (N.reflexive _) (N.reflexive _)))
    (N.s-zeta (N.reflexive _) (N.reflexive _) (N.reflexive _))

strong-beta-join :
  ∃ λ w → N._⇛_ beta-left w × N._⇛_ beta-right w
strong-beta-join = C.diamond beta-root beta-congruence

wide-compatibility :
  ∃ λ w → L.Par._⇉*_ beta-left w × L.Par._⇉*_ beta-right w
wide-compatibility = C.⇉-diamond (N.embed beta-root) (N.embed beta-congruence)

-- Duplication: substituting a reducible argument at two positions is
-- still ONE strict-parallel step, not merely a multi-step consequence.
duplicates : Term
duplicates = tm-ctor "Pair" (tm-var 0 ∷ tm-var 0 ∷ [])

duplicated-substitution :
  N._⇛_ (substTopT argument duplicates) (substTopT seven duplicates)
duplicated-substitution =
  C.substitute-top (N.s-zeta (N.reflexive _) (N.reflexive _) (N.reflexive _))
    (N.reflexive duplicates)

-- A two-step branch path with a NEWLY EXPOSED redex: the outer function
-- is an application, not a lambda, before the first beta contraction.
identity : Term
identity = tm-lam unrestricted tm-int_type (tm-var 0)

take-identity : Term
take-identity = tm-lam unrestricted
  (tm-pi unrestricted tm-int_type tm-int_type) (tm-var 0)

branch-body : Term
branch-body = tm-app (tm-app take-identity identity) (tm-var 0)

branch-two-steps : _⇝*_ L.empty-sig branch-body (tm-var 0)
branch-two-steps = ⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)

not-one-strict-step : N._⇛_ branch-body (tm-var 0) → ⊥
not-one-strict-step ()

branch-strict-path : Star N._⇛_ branch-body (tm-var 0)
branch-strict-path = N.from-small-star branch-two-steps

fields : List Term
fields = wrap seven ∷ wrap nine ∷ []

case-peak : Term
case-peak = tm-case (tm-ctor "Pair" fields) tm-int_type
  (("Pair" , 2 , branch-body) ∷ [])

case-left case-right : Term
case-left = substArgs fields branch-body
case-right = tm-case (tm-ctor "Pair" (seven ∷ nine ∷ [])) tm-int_type
  (("Pair" , 2 , tm-var 0) ∷ [])

case-root : _⇝*_ L.empty-sig case-peak case-left
case-root = ⇝*-step (ι refl refl) ⇝*-refl

case-other-path : _⇝*_ L.empty-sig case-peak case-right
case-other-path =
  ⇝*-step (ξ-case-brs (⇝ᵇ-cons branch-two-steps ⇝ᵇ-nil))
    (⇝*-step (ξ-case (ξ-ctor-at (suc zero) ζ))
      (⇝*-step (ξ-case (ξ-ctor-at zero ζ)) ⇝*-refl))

case-multi-step-join :
  ∃ λ w → _⇝*_ L.empty-sig case-left w × _⇝*_ L.empty-sig case-right w
case-multi-step-join = C.confluence case-root case-other-path

-- The non-head field is distinguishable; field zero is the last value, 9.
case-right-contracts : _⇝_ L.empty-sig case-right nine
case-right-contracts = ι refl refl

-- Each compact-literal root participates in a genuine strong peak.
strict-z : N._⇛_ L.z-case L.result
strict-z = N.s-nat-zero refl (N.reflexive _) (N.branches-refl _)
strict-s : N._⇛_ L.s-case (tm-nat_lit 7)
strict-s = N.s-nat-suc refl (N.reflexive _) (N.branches-refl _)
strict-first : N._⇛_ L.first-case L.result
strict-first = N.s-bounded-zero refl (N.reflexive _) (N.branches-refl _)
strict-next : N._⇛_ L.next-case L.result
strict-next = N.s-bounded-suc refl (N.reflexive _) (N.branches-refl _)

z-join : ∃ λ w → N._⇛_ L.result w × N._⇛_ L.z-case w
z-join = C.diamond strict-z (N.reflexive _)
s-join : ∃ λ w → N._⇛_ (tm-nat_lit 7) w × N._⇛_ L.s-case w
s-join = C.diamond strict-s (N.reflexive _)
first-join : ∃ λ w → N._⇛_ L.result w × N._⇛_ L.first-case w
first-join = C.diamond strict-first (N.reflexive _)
next-join : ∃ λ w → N._⇛_ L.result w × N._⇛_ L.next-case w
next-join = C.diamond strict-next (N.reflexive _)

wrong-z : ∀ {u} → N._⇛_ L.wrong-z u → u ≡ L.result → ⊥
wrong-z p eq = L.wrong-z-parallel-rejected (N.embed p) eq
wrong-s : ∀ {u} → N._⇛_ L.wrong-s u → u ≡ L.result → ⊥
wrong-s p eq = L.wrong-s-parallel-rejected (N.embed p) eq
wrong-first : ∀ {u} → N._⇛_ L.wrong-first u → u ≡ L.result → ⊥
wrong-first p eq = L.wrong-first-parallel-rejected (N.embed p) eq
wrong-next : ∀ {u} → N._⇛_ L.wrong-next u → u ≡ L.result → ⊥
wrong-next p eq = L.wrong-next-parallel-rejected (N.embed p) eq

-- Nonempty, recursive delta table: closedness is NOT termination.
loop-sig : Signature
loop-sig = record { body = λ _ → just (tm-global "loop") ; type-of = λ _ → nothing }

loop-closed : ClosedBody loop-sig
loop-closed refl = sc-global

module Loop = Conf loop-sig (λ {f} {body′} p → loop-closed {f} {body′} p)

loop-self-step : _⇝_ loop-sig (tm-global "loop") (tm-global "loop")
loop-self-step = δ refl

delta-join : ∃ λ w → _⇝*_ loop-sig (tm-global "loop") w
  × _⇝*_ loop-sig (tm-global "loop") w
delta-join = Loop.confluence
  (⇝*-step (δ {f = "entry"} refl) ⇝*-refl)
  (⇝*-step (δ {f = "entry"} refl) (⇝*-step loop-self-step ⇝*-refl))

seven-normal : C.NormalForm seven
seven-normal ()
beta-root-normalizes : _⇝*_ L.empty-sig beta-peak seven
beta-root-normalizes = ⇝*-step β (⇝*-step ζ (⇝*-step ζ ⇝*-refl))

beta-congruence-normalizes : _⇝*_ L.empty-sig beta-peak seven
beta-congruence-normalizes =
  ⇝*-step (ξ-app₁ (ξ-lam-body ζ))
    (⇝*-step (ξ-app₂ ζ) (⇝*-step β ⇝*-refl))

normal-uniqueness : seven ≡ seven
normal-uniqueness = C.normal-forms-unique
  beta-root-normalizes beta-congruence-normalizes seven-normal seven-normal
