{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Checked admission plus positive case execution/readback preserves the
-- ORIGINAL closed expected goal. Neither execution nor readback types it.
------------------------------------------------------------------------
module Proof.ClosureCaseSafety where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Core.Syntax using (Term)
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller
import Core.ClosureEval as E
import Core.ClosureCase as Case
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureCase as Model
import Proof.Substitution as Substitution

module Safe {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  module C = R.C
  module Simulation = Model.Simulation C.W.sig

  safe-execution : ∀ {request value} (admitted : R.Checked request)
    → Case.Executes [] (R.Checked.closed-subject admitted) value
    → Σ Term (λ result → Meaning.Denotes 0 value result ×
      C.Sound.SafeState result (R.Checked.closed-goal admitted))
  safe-execution admitted execution with Simulation.evaluate {d = 0} Meaning.d[] execution
  ... | result , denoted , path = result , denoted ,
    R.Checked.trace-safe admitted
      (Simulation.O.⇝*-source (Substitution.substS-idSub (R.Checked.closed-subject admitted)) path)

  safe-quotation : ∀ {request value quoted} (admitted : R.Checked request)
    → Case.Executes [] (R.Checked.closed-subject admitted) value → Q.Quoted 0 value quoted
    → Q.BetaZetaNormal quoted × C.Sound.SafeState quoted (R.Checked.closed-goal admitted)
  safe-quotation admitted execution quoted = Q.quoted-normal quoted ,
    R.Checked.trace-safe admitted
      (Simulation.O.⇝*-source (Substitution.substS-idSub (R.Checked.closed-subject admitted))
        (Simulation.quotation Scope.s[] (R.N.Admitted.term-scoped (R.Checked.admitted admitted))
          Meaning.d[] execution quoted))

  run-safe : ∀ {request} (fuel : ℕ) (admitted : R.Checked request)
    → Case.Result (Σ E.Value (λ value → Σ Term (λ result →
        Meaning.Denotes 0 value result × C.Sound.SafeState result (R.Checked.closed-goal admitted))))
  run-safe fuel admitted with Case.run fuel (R.Checked.closed-subject admitted) []
  ... | Case.stop reason = Case.stop reason
  ... | Case.done (value , execution) with safe-execution admitted execution
  ... | result , denoted , safe = Case.done (value , result , denoted , safe)
