{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Checked source/caller admission + positive modeled evaluation -> native
-- safety at the SAME closed goal. No executable totality or Quote oracle.
------------------------------------------------------------------------
module Proof.ClosureEvaluationSafety where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Core.Syntax using (Term)
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller
import Core.ClosureEval as E
import Proof.ClosureEvaluation as Meaning
import Proof.Substitution as Substitution

module Safe {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  module C = R.C
  module Model = Meaning.Simulation C.W.sig
  safe-evaluation : ∀ {request value} (admitted : R.Checked request)
    → E.Evaluates [] (R.Checked.closed-subject admitted) value
    → Σ Term (λ result → Meaning.Denotes 0 value result × C.Sound.SafeState result (R.Checked.closed-goal admitted))
  safe-evaluation admitted evaluated with Model.evaluate {depth = 0} Meaning.d[] evaluated
  ... | result , denoted , path = result , denoted ,
    C.Sound.trace-safe (R.N.Admitted.checked (R.Checked.admitted admitted)) (R.Checked.final admitted)
      (Model.O.⇝*-source (Substitution.substS-idSub (R.Checked.closed-subject admitted)) path)

  -- Failure/exhaustion is retained as a MODEL outcome, not relabelled as
  -- a proof of divergence, ill-typing or an actual Elixir exception.
  run-safe : ∀ {request} (fuel : ℕ) (admitted : R.Checked request)
    → E.Result (Σ E.Value (λ value → Σ Term
        (λ result → Meaning.Denotes 0 value result × C.Sound.SafeState result (R.Checked.closed-goal admitted))))
  run-safe fuel admitted with E.run fuel (R.Checked.closed-subject admitted) []
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with safe-evaluation admitted evaluated
  ... | result , denoted , safe = E.done (value , result , denoted , safe)
