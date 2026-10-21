------------------------------------------------------------------------
-- Regressions for structurally checked spine lifting.
-- No confluence theorem, typing oracle, or termination override is used.
-- Two real let steps update a non-head field while its neighbours and the
-- opposite data spine remain unchanged.
------------------------------------------------------------------------
module Proof.SpineLifting where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Grade using (unrestricted)
open import Core.Syntax
open import Core.Reduction
import Core.Parallel as P

sig : Signature
sig = record { body = λ _ → nothing ; type-of = λ _ → nothing }

module Par = P.Par sig

finish : Term
finish = tm-nat_lit 42

inner : Term
inner = tm-let unrestricted tm-int_type finish (tm-var 0)

start : Term
start = tm-let unrestricted tm-int_type inner (tm-var 0)

two-steps : _⇝*_ sig start finish
two-steps = ⇝*-step ζ (⇝*-step ζ ⇝*-refl)

two-parallel : Par._⇉*_ start finish
two-parallel =
  Par.⇉*-step (Par.⇝→⇉ ζ) (Par.⇉*-step (Par.⇝→⇉ ζ) Par.⇉*-refl)

before : List Term
before = tm-nat_lit 11 ∷ start ∷ tm-nat_lit 99 ∷ []

after : List Term
after = tm-nat_lit 11 ∷ finish ∷ tm-nat_lit 99 ∷ []

fixed : List Term
fixed = tm-nat_lit 7 ∷ []

parallel-ctor : Par._⇉*_ (tm-ctor "C" before) (tm-ctor "C" after)
parallel-ctor = Par.⇉*-at-ctor before (suc zero) two-parallel

parallel-params : Par._⇉*_ (tm-data "D" before fixed) (tm-data "D" after fixed)
parallel-params = Par.⇉*-at-data-params before (suc zero) two-parallel

parallel-indices : Par._⇉*_ (tm-data "D" fixed before) (tm-data "D" fixed after)
parallel-indices = Par.⇉*-at-data-indices before (suc zero) two-parallel

small-ctor : _⇝*_ sig (tm-ctor "C" before) (tm-ctor "C" after)
small-ctor = Par.⇝*-at-ctor before (suc zero) two-steps

small-params : _⇝*_ sig (tm-data "D" before fixed) (tm-data "D" after fixed)
small-params = Par.⇝*-at-params before (suc zero) two-steps

small-indices : _⇝*_ sig (tm-data "D" fixed before) (tm-data "D" fixed after)
small-indices = Par.⇝*-at-indices before (suc zero) two-steps

-- Zero-step paths still return the unchanged enclosing term.
parallel-zero : Par._⇉*_ (tm-ctor "C" before) (tm-ctor "C" before)
parallel-zero = Par.⇉*-at-ctor before (suc zero) Par.⇉*-refl

small-zero : _⇝*_ sig (tm-data "D" fixed before) (tm-data "D" fixed before)
small-zero = Par.⇝*-at-indices before (suc zero) ⇝*-refl

-- Exercise the explicit source-alignment argument on a symbolic path.
parallel-aligned : ∀ {u} → start ≡ u → Par._⇉*_ u finish
  → Par._⇉*_ (tm-ctor "C" before) (tm-ctor "C" after)
parallel-aligned eq path =
  Par.⇉*-at-spine (tm-ctor "C")
    (λ {xs} i step → Par.p-ctor-at xs i step) path before (suc zero) eq

small-aligned : ∀ {u} → start ≡ u → _⇝*_ sig u finish
  → _⇝*_ sig (tm-ctor "C" before) (tm-ctor "C" after)
small-aligned eq path =
  Par.⇝*-at-spine (tm-ctor "C")
    (λ i step → ξ-ctor-at i step) path before (suc zero) eq

-- The complete parallel-to-small-step simulation is termination-checked,
-- including its constructor-spine conversion and multi-step wrappers.
converted-parallel : _⇝*_ sig (tm-ctor "C" before) (tm-ctor "C" after)
converted-parallel = Par.⇉→⇝*-star parallel-ctor
