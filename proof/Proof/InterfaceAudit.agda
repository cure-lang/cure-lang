------------------------------------------------------------------------
-- Regression witnesses for UNSATISFIABLE legacy soundness hypotheses.
--
-- These are refutations of interfaces, not assumptions of a soundness
-- theorem. Type-checking the legacy parameterised modules does not make
-- their hypotheses jointly inhabitable. Keep these witnesses until the
-- corresponding interfaces are replaced, then retain their old shapes
-- locally as negative regression specifications.
------------------------------------------------------------------------
module Proof.InterfaceAudit where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Typing using (Conversion; ∈-here)
open import Proof.Progress using (BuiltinCtors; allCtorNames)
open import Proof.Preservation using (ClosedSig; ReduceConv)

-- Frozen historical interface; no active theorem accepts this oracle.
Covers : IndEnv → Set
Covers ind = ∀ (brs : List Branch) (m : Term)
           → (∀ (c : Name) → c ∈ allCtorNames (IndEnv.families ind)
             → ∃ λ ar → ∃ λ b
             → findBranch c brs ≡ just (c , ar , b) × (c , ar , b) ∈ brs)

-- The historical Covers required a Z branch even in the empty list.
covers-incompatible-with-builtins :
  ∀ ind → Covers ind → BuiltinCtors ind → ⊥
covers-incompatible-with-builtins ind cov bc
  with cov [] tm-int_type "Z" (proj₁ bc)
... | ar , b , () , member

-- A let can reduce to a Pi without being syntactically a Pi.
pi-type : Term
pi-type = tm-pi unrestricted tm-int_type tm-int_type

let-pi : Term
let-pi = tm-let unrestricted (tm-type l0) pi-type (tm-var zero)

let-pi-step : ∀ sig → _⇝_ sig let-pi pi-type
let-pi-step sig = ζ

let-not-pi : ∀ g d c → let-pi ≡ tm-pi g d c → ⊥
let-not-pi g d c ()

reflection-incompatible-with-reduction :
  ∀ sig (conv : Conversion) → ReduceConv sig conv → ⊥
reflection-incompatible-with-reduction sig conv rc
  with Conversion.≈-pi-inj conv
    (Conversion.≈-sym conv (rc (let-pi-step sig)))
... | g , d , c , eq = let-not-pi g d c eq

-- ClosedSig quantifies over this fabricated family, independently of ind.
-- Its first parameter refers to variable zero, which is not scoped at 0.
open-family : Family
open-family = record
  { fam-name = "audit-open"
  ; fam-params = ("x" , tm-var zero) ∷ []
  ; fam-indices = []
  ; fam-level = l0
  ; fam-ctors = []
  ; universe-ok = true
  ; positive = true
  }

var0-not-closed : Scoped 0 (tm-var zero) → ⊥
var0-not-closed (sc-var ())

closedSig-impossible : ∀ ind sig → ClosedSig ind sig → ⊥
closedSig-impossible ind sig closed =
  var0-not-closed (proj₁ (proj₂ closed) open-family ∈-here)

-- Frozen historical interface: no active theorem takes this parameter.
LiteralArity : Set
LiteralArity =
    (∀ {brs : List Branch} {ar b} → findBranch "Z" brs ≡ just ("Z" , ar , b) → 0 ≡ ar)
  × (∀ {brs : List Branch} {ar b} → findBranch "S" brs ≡ just ("S" , ar , b) → 1 ≡ ar)
  × (∀ {brs : List Branch} {ar b} → findBranch "First" brs ≡ just ("First" , ar , b) → 1 ≡ ar)
  × (∀ {brs : List Branch} {ar b} → findBranch "Next" brs ≡ just ("Next" , ar , b) → 2 ≡ ar)

-- LiteralArity had the same global-quantification problem as Covers.
-- A raw Z branch can declare arity one; typing must reject that branch,
-- rather than a confluence theorem assuming that raw syntax cannot exist.
zero-not-one : zero ≡ 1 → ⊥
zero-not-one ()

literalArity-impossible : LiteralArity → ⊥
literalArity-impossible la =
  zero-not-one (proj₁ la {brs = ("Z" , 1 , tm-int_type) ∷ []} refl)
