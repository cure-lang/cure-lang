------------------------------------------------------------------------
-- Different normal forms are NOT a proof of non-convertibility: eta,
-- residual delta and broader executable comparison are separate.
------------------------------------------------------------------------
module Core.NormalFormComparison where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Core.Signature using (IndEnv)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (yes; no)
open import Core.Syntax using (Term)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.SyntaxEquality as Syntax

record EqualNormal (depth : ℕ) (env : List E.Value) (left right : Term) : Set where
  field
    common : Term
    left-execution : Q.Normalizes depth env left common
    right-execution : Q.Normalizes depth env right common
  normal : Q.BetaZetaNormal common
  normal = Q.quoted-normal (Q.Normalizes.quoted left-execution)

record DistinctNormal (depth : ℕ) (env : List E.Value) (left right : Term) : Set where
  field
    left-form right-form : Term
    left-execution : Q.Normalizes depth env left left-form
    right-execution : Q.Normalizes depth env right right-form
    different-syntax : left-form ≢ right-form

data Side : Set where
  left-side right-side : Side
data Verdict (depth : ℕ) (env : List E.Value) (left right : Term) : Set where
  same : EqualNormal depth env left right → Verdict depth env left right
  distinct : DistinctNormal depth env left right → Verdict depth env left right
  unknown : Side → E.Failure → Verdict depth env left right
data Classification : Set where
  equal-forms distinct-forms inconclusive : Classification
classify : ∀ {depth env left right} → Verdict depth env left right → Classification
classify (same evidence) = equal-forms
classify (distinct evidence) = distinct-forms
classify (unknown side reason) = inconclusive

compare-in : Maybe IndEnv → (fuel depth : ℕ) (env : List E.Value) (left right : Term)
  → Verdict depth env left right
compare-in mode fuel depth env left right with Q.normalise-in mode fuel depth left env
... | E.stop reason = unknown left-side reason
... | E.done (l , left-execution) with Q.normalise-in mode fuel depth right env
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
