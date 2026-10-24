------------------------------------------------------------------------
-- Opt-in positive residual comparison. Syntactic difference is NOT
-- non-conversion: eta, certified delta and broader policies are separate.
------------------------------------------------------------------------
module Core.ResidualComparison where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (yes; no)
open import Core.Signature using (IndEnv)
open import Core.Syntax using (Term; Scoped)
open import Core.NormalFormComparison public using
  (Side; left-side; right-side; Classification; equal-forms; distinct-forms; inconclusive)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.SyntaxEquality as Syntax

record EqualResidual (depth : ℕ) (env : List E.Value) (left right : Term) : Set where
  field
    common : Term
    left-execution : Q.ResidualNormalizes depth env left common
    right-execution : Q.ResidualNormalizes depth env right common
  scoped : Scoped depth common
  scoped = Q.quoted-scoped (Q.ResidualNormalizes.quoted left-execution)

record DistinctResidual (depth : ℕ) (env : List E.Value) (left right : Term) : Set where
  field
    left-form right-form : Term
    left-execution : Q.ResidualNormalizes depth env left left-form
    right-execution : Q.ResidualNormalizes depth env right right-form
    different-syntax : left-form ≢ right-form

data Verdict (depth : ℕ) (env : List E.Value) (left right : Term) : Set where
  same : EqualResidual depth env left right → Verdict depth env left right
  distinct : DistinctResidual depth env left right → Verdict depth env left right
  unknown : Side → E.Failure → Verdict depth env left right
classify : ∀ {depth env left right} → Verdict depth env left right → Classification
classify (same evidence) = equal-forms
classify (distinct evidence) = distinct-forms
classify (unknown side reason) = inconclusive

compare-in : Maybe IndEnv → (fuel depth : ℕ) (env : List E.Value) (left right : Term)
  → Verdict depth env left right
compare-in mode fuel depth env left right with Q.normalise-residual-in mode fuel depth left env
... | E.stop reason = unknown left-side reason
... | E.done (l , left-execution) with Q.normalise-residual-in mode fuel depth right env
... | E.stop reason = unknown right-side reason
... | E.done (r , right-execution) with Syntax.equal? l r
... | no different = distinct record
  { left-form = l ; right-form = r ; left-execution = left-execution
  ; right-execution = right-execution ; different-syntax = different }
... | yes refl = same record
  { common = l ; left-execution = left-execution ; right-execution = right-execution }
compare : (fuel depth : ℕ) (env : List E.Value) (left right : Term) → Verdict depth env left right
compare = compare-in nothing
compare-with : IndEnv → (fuel depth : ℕ) (env : List E.Value) (left right : Term) → Verdict depth env left right
compare-with ind = compare-in (just ind)
