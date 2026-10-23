------------------------------------------------------------------------
-- Checked top-level data-head readback of flattened closure values.
-- Layout and field readback are checked; typing is a separate replay.
-- Compatibility layer: fields use signature-free closure readback.
-- Shared signature-aware APIs additionally handle recursive data.
------------------------------------------------------------------------
module Core.DataReadback where

open import Data.List using (List)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Core.Syntax
open import Core.Signature using (IndEnv)
import Core.DataSpine as Layout
import Core.ClosureEval as E
import Core.ClosureQuote as Q

record Output (depth : ℕ) (ind : IndEnv) (name : Name) (values : List E.Value) : Set where
  constructor readback
  field
    alignment : Layout.Alignment ind name values
    parameters indices : List Term
    parameters-quoted : Q.SpineQuoted depth (Layout.Alignment.parameters alignment) parameters
    indices-quoted : Q.SpineQuoted depth (Layout.Alignment.indices alignment) indices
  term : Term
  term = tm-data name parameters indices
  scoped : Scoped depth term
  scoped = sc-data (Q.spine-scoped parameters-quoted) (Q.spine-scoped indices-quoted)

data Failure : Set where
  exhausted : Failure
  layout-failure : Layout.Failure → Failure
  field-failure : E.Failure → Failure
data Result (A : Set) : Set where
  done : A → Result A
  stop : Failure → Result A
run : (fuel depth : ℕ) (ind : IndEnv) (name : Name) (values : List E.Value)
  → Result (Output depth ind name values)
run zero depth ind name values = stop exhausted
run (suc fuel) depth ind name values with Layout.check ind name values
... | Layout.rejected reason = stop (layout-failure reason)
... | Layout.accepted layout
  with Q.spine-run fuel depth (Layout.Alignment.parameters layout)
... | E.stop reason = stop (field-failure reason)
... | E.done (ps , params) with Q.spine-run fuel depth (Layout.Alignment.indices layout)
... | E.stop reason = stop (field-failure reason)
... | E.done (is , indices) = done (readback layout ps is params indices)
