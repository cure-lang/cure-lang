------------------------------------------------------------------------
-- Bounded TOP-LEVEL neutral-case MODEL component. Motive and every branch
-- share the indexed caller environment. The old shared value/strict quote
-- APIs are unchanged; nested residual contents can still be unsupported.
------------------------------------------------------------------------
module Core.NeutralCase where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Signature using (IndEnv)
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.BranchOpening as Opening

record Captured (env : List E.Value) (scrutinee : Term) : Set where
  constructor captured
  field
    head : E.Neutral
    evaluated : E.Evaluates env scrutinee (E.v-neutral head)

data BranchesRead (depth : ℕ) (env : List E.Value) : List Branch → List Branch → Set where
  b[] : BranchesRead depth env [] []
  b∷ : ∀ {name ar body quoted rest results}
    → Q.Normalizes (ar + depth) (Opening.environment depth ar env) body quoted
    → BranchesRead depth env rest results
    → BranchesRead depth env ((name , ar , body) ∷ rest) ((name , ar , quoted) ∷ results)

metadata : List Branch → List (Σ Name λ _ → ℕ)
metadata [] = []
metadata ((name , ar , body) ∷ rest) = (name , ar) ∷ metadata rest
metadata-preserved : ∀ {d env branches results} → BranchesRead d env branches results
  → metadata branches ≡ metadata results
metadata-preserved b[] = refl
metadata-preserved (b∷ {name = name} {ar = ar} head tail) =
  cong ((name , ar) ∷_) (metadata-preserved tail)

record Readback (depth : ℕ) (env : List E.Value) (scrutinee motive : Term) (branches : List Branch)
  (cap : Captured env scrutinee) : Set where
  constructor readback
  field
    scrutinee-form motive-form : Term
    branch-forms : List Branch
    head-quoted : Q.NeutralQuoted depth (Captured.head cap) scrutinee-form
    motive-execution : Q.Normalizes depth env motive motive-form
    branches-read : BranchesRead depth env branches branch-forms
  term : Term
  term = tm-case scrutinee-form motive-form branch-forms

data Failure : Set where
  exhausted not-neutral : Failure
  capture-failure head-failure motive-failure : E.Failure → Failure
  branch-failure : Name → ℕ → E.Failure → Failure
data Result (A : Set) : Set where
  done : A → Result A
  stop : Failure → Result A

capture-in : Maybe IndEnv → (fuel : ℕ) (env : List E.Value) (scrutinee : Term)
  → Result (Captured env scrutinee)
capture-in mode zero env scrutinee = stop exhausted
capture-in mode (suc fuel) env scrutinee with E.run-in mode fuel scrutinee env
... | E.stop reason = stop (capture-failure reason)
... | E.done (E.v-neutral head , evaluated) = done (captured head evaluated)
... | E.done (other , evaluated) = stop not-neutral

branches-in : Maybe IndEnv → (fuel depth : ℕ) (env : List E.Value) (branches : List Branch)
  → Result (Σ (List Branch) (BranchesRead depth env branches))
branches-in mode zero depth env branches = stop exhausted
branches-in mode (suc fuel) depth env [] = done ([] , b[])
branches-in mode (suc fuel) depth env ((name , ar , body) ∷ rest)
  with Q.normalise-in mode fuel (ar + depth) body (Opening.environment depth ar env)
... | E.stop reason = stop (branch-failure name ar reason)
... | E.done (quoted , execution) with branches-in mode fuel depth env rest
... | stop reason = stop reason
... | done (results , tail) = done ((name , ar , quoted) ∷ results , b∷ execution tail)

readback-in : Maybe IndEnv → (fuel depth : ℕ) (env : List E.Value) (scrutinee motive : Term)
  (branches : List Branch) (cap : Captured env scrutinee) → Result (Readback depth env scrutinee motive branches cap)
readback-in mode zero depth env scrutinee motive branches cap = stop exhausted
readback-in mode (suc fuel) depth env scrutinee motive branches cap
  with Q.neutral-run-in mode fuel depth (Captured.head cap)
... | E.stop reason = stop (head-failure reason)
... | E.done (s , head-quoted) with Q.normalise-in mode fuel depth motive env
... | E.stop reason = stop (motive-failure reason)
... | E.done (m , normalized-motive) with branches-in mode fuel depth env branches
... | stop reason = stop reason
... | done (brs , normalized-branches) = done (readback s m brs head-quoted normalized-motive normalized-branches)

normalise-in : Maybe IndEnv → (fuel depth : ℕ) (env : List E.Value) (scrutinee motive : Term)
  (branches : List Branch) → Result (Σ (Captured env scrutinee) λ cap → Readback depth env scrutinee motive branches cap)
normalise-in mode zero depth env scrutinee motive branches = stop exhausted
normalise-in mode (suc fuel) depth env scrutinee motive branches with capture-in mode fuel env scrutinee
... | stop reason = stop reason
... | done cap with readback-in mode fuel depth env scrutinee motive branches cap
... | stop reason = stop reason
... | done output = done (cap , output)

normalise : (fuel depth : ℕ) (env : List E.Value) (scrutinee motive : Term) (branches : List Branch)
  → Result (Σ (Captured env scrutinee) λ cap → Readback depth env scrutinee motive branches cap)
normalise = normalise-in nothing
normalise-with : IndEnv → (fuel depth : ℕ) (env : List E.Value) (scrutinee motive : Term) (branches : List Branch)
  → Result (Σ (Captured env scrutinee) λ cap → Readback depth env scrutinee motive branches cap)
normalise-with ind = normalise-in (just ind)
