------------------------------------------------------------------------
-- Literal-case arities are LOCAL reduction premises.
--
-- Correctly shaped branches contract; wrong-arity branches cannot contract
-- to the tested literal in either small-step or parallel reduction.
-- This is not a claim that a malformed case has no congruence/self step.
------------------------------------------------------------------------
module Proof.LiteralCases where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Grade using (unrestricted)
open import Core.Syntax
open import Core.Reduction
import Core.Parallel as P
open import Proof.Confluence using (ClosedBody; module Conf)

empty-sig : Signature
empty-sig = record { body = λ _ → nothing ; type-of = λ _ → nothing }

empty-closed : ClosedBody empty-sig
empty-closed ()

module Par = P.Par empty-sig
module Confluent = Conf empty-sig
  (λ {f} {body′} eq → empty-closed {f = f} {body′ = body′} eq)

result : Term
result = tm-nat_lit 42

z-case : Term
z-case = tm-case (tm-nat_lit 0) tm-int_type (("Z" , 0 , result) ∷ [])

s-case : Term
s-case = tm-case (tm-nat_lit 8) tm-int_type (("S" , 1 , tm-var 0) ∷ [])

first-case : Term
first-case = tm-case (tm-bounded_lit 0) tm-int_type (("First" , 1 , result) ∷ [])

next-case : Term
next-case = tm-case (tm-bounded_lit 8) tm-int_type (("Next" , 2 , result) ∷ [])

z-contracts : _⇝_ empty-sig z-case result
z-contracts = ι-nat-zero refl refl

s-contracts : _⇝_ empty-sig s-case (tm-nat_lit 7)
s-contracts = ι-nat-suc refl refl

first-contracts : _⇝_ empty-sig first-case result
first-contracts = ι-bounded-zero refl refl

next-contracts : _⇝_ empty-sig next-case result
next-contracts = ι-bounded-suc refl refl

wrong-z : Term
wrong-z = tm-case (tm-nat_lit 0) tm-int_type (("Z" , 1 , result) ∷ [])

wrong-s : Term
wrong-s = tm-case (tm-nat_lit 8) tm-int_type (("S" , 0 , result) ∷ [])

wrong-first : Term
wrong-first = tm-case (tm-bounded_lit 0) tm-int_type (("First" , 0 , result) ∷ [])

wrong-next : Term
wrong-next = tm-case (tm-bounded_lit 8) tm-int_type (("Next" , 1 , result) ∷ [])

wrong-z-rejected : ∀ {u} → _⇝_ empty-sig wrong-z u → u ≡ result → ⊥
wrong-z-rejected (ι-nat-zero refl ()) eq
wrong-z-rejected (ξ-case ()) eq
wrong-z-rejected (ξ-case-motive ()) eq
wrong-z-rejected (ξ-case-brs steps) ()

wrong-s-rejected : ∀ {u} → _⇝_ empty-sig wrong-s u → u ≡ result → ⊥
wrong-s-rejected (ι-nat-suc refl ()) eq
wrong-s-rejected (ξ-case ()) eq
wrong-s-rejected (ξ-case-motive ()) eq
wrong-s-rejected (ξ-case-brs steps) ()

wrong-first-rejected : ∀ {u} → _⇝_ empty-sig wrong-first u → u ≡ result → ⊥
wrong-first-rejected (ι-bounded-zero refl ()) eq
wrong-first-rejected (ξ-case ()) eq
wrong-first-rejected (ξ-case-motive ()) eq
wrong-first-rejected (ξ-case-brs steps) ()

wrong-next-rejected : ∀ {u} → _⇝_ empty-sig wrong-next u → u ≡ result → ⊥
wrong-next-rejected (ι-bounded-suc refl ()) eq
wrong-next-rejected (ξ-case ()) eq
wrong-next-rejected (ξ-case-motive ()) eq
wrong-next-rejected (ξ-case-brs steps) ()

-- Small-step inclusion preserves the new witnesses.
z-parallel : Par._⇉_ z-case result
z-parallel = Par.⇝→⇉ z-contracts

s-parallel : Par._⇉_ s-case (tm-nat_lit 7)
s-parallel = Par.⇝→⇉ s-contracts

first-parallel : Par._⇉_ first-case result
first-parallel = Par.⇝→⇉ first-contracts

next-parallel : Par._⇉_ next-case result
next-parallel = Par.⇝→⇉ next-contracts

wrong-z-parallel-rejected : ∀ {u} → Par._⇉_ wrong-z u → u ≡ result → ⊥
wrong-z-parallel-rejected (Par.p-ι-nat-zero {b′ = b′} found refl sm brs bodies) eq
  with Par.findBranch-⇉*ᵇ-rev "Z" 0 b′ brs found
... | b , () , steps
wrong-z-parallel-rejected (Par.p-case _ _ _) ()

wrong-s-parallel-rejected : ∀ {u} → Par._⇉_ wrong-s u → u ≡ result → ⊥
wrong-s-parallel-rejected (Par.p-ι-nat-suc {b′ = b′} found refl sm brs bodies) eq
  with Par.findBranch-⇉*ᵇ-rev "S" 1 b′ brs found
... | b , () , steps
wrong-s-parallel-rejected (Par.p-case _ _ _) ()

wrong-first-parallel-rejected : ∀ {u} → Par._⇉_ wrong-first u → u ≡ result → ⊥
wrong-first-parallel-rejected (Par.p-ι-bounded-zero {b′ = b′} found refl sm brs bodies) eq
  with Par.findBranch-⇉*ᵇ-rev "First" 1 b′ brs found
... | b , () , steps
wrong-first-parallel-rejected (Par.p-case _ _ _) ()

wrong-next-parallel-rejected : ∀ {u} → Par._⇉_ wrong-next u → u ≡ result → ⊥
wrong-next-parallel-rejected (Par.p-ι-bounded-suc {b′ = b′} found refl sm brs bodies) eq
  with Par.findBranch-⇉*ᵇ-rev "Next" 2 b′ brs found
... | b , () , steps
wrong-next-parallel-rejected (Par.p-case _ _ _) ()

-- A genuine peak: contract the literal case first, or reduce its branch's
-- let first. Conf now has a concrete ClosedBody instance and no impossible
-- literal-arity parameter. The one remaining confluence termination
-- override is audited; this example does not discharge that obligation.
branch-let : Term
branch-let = tm-let unrestricted tm-int_type result (tm-var 0)

peak : Term
peak = tm-case (tm-nat_lit 0) tm-int_type (("Z" , 0 , branch-let) ∷ [])

literal-peak-joins :
  ∃ λ w → _⇝*_ empty-sig branch-let w × _⇝*_ empty-sig z-case w
literal-peak-joins =
  Confluent.confluence {t = peak}
    (⇝*-step (ι-nat-zero refl refl) ⇝*-refl)
    (⇝*-step (ξ-case-brs (⇝ᵇ-cons (⇝*-step ζ ⇝*-refl) ⇝ᵇ-nil)) ⇝*-refl)

-- Independently build the same join without invoking the legacy
-- confluence recursion or any termination override.
literal-peak-joins-direct :
  ∃ λ w → _⇝*_ empty-sig branch-let w × _⇝*_ empty-sig z-case w
literal-peak-joins-direct =
  result , ⇝*-step ζ ⇝*-refl , ⇝*-step (ι-nat-zero refl refl) ⇝*-refl
