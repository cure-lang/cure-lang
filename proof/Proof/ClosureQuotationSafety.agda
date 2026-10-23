{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Checked caller admission -> positive evaluate/quote -> a scoped
-- beta/zeta-normal native safe state at the SAME closed expected goal.
-- No unbounded totality, eta, delta-normality or Quote oracle is assumed.
------------------------------------------------------------------------
module Proof.ClosureQuotationSafety where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Core.Syntax using (Term)
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller
import Core.ClosureEval as E
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quotation
import Proof.Substitution as Substitution

module Safe {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  module C = R.C
  module Model = Quotation.Simulation C.W.sig

  safe-normalization : ∀ {request quoted} (admitted : R.Checked request)
    → Q.Normalizes 0 [] (R.Checked.closed-subject admitted) quoted
    → Q.BetaZetaNormal quoted × C.Sound.SafeState quoted (R.Checked.closed-goal admitted)
  safe-normalization admitted execution =
    Q.quoted-normal (Q.Normalizes.quoted execution) ,
    C.Sound.trace-safe (R.N.Admitted.checked (R.Checked.admitted admitted)) (R.Checked.final admitted)
      (Model.O.⇝*-source (Substitution.substS-idSub (R.Checked.closed-subject admitted))
        (Model.normalization Scope.s[] (R.N.Admitted.term-scoped (R.Checked.admitted admitted))
          Meaning.d[] execution))

  run-safe : ∀ {request} (fuel : ℕ) (admitted : R.Checked request)
    → E.Result (Σ Term (λ quoted →
        Q.Normalizes 0 [] (R.Checked.closed-subject admitted) quoted
        × Q.BetaZetaNormal quoted × C.Sound.SafeState quoted (R.Checked.closed-goal admitted)))
  run-safe fuel admitted with Q.normalise fuel 0 (R.Checked.closed-subject admitted) []
  ... | E.stop reason = E.stop reason
  ... | E.done (quoted , execution) with safe-normalization admitted execution
  ... | normal , safe = E.done (quoted , execution , normal , safe)

  run-safe-with : ∀ {request} (fuel : ℕ) (admitted : R.Checked request)
    → E.Result (Σ Term (λ quoted →
        Q.Normalizes 0 [] (R.Checked.closed-subject admitted) quoted
        × Q.BetaZetaNormal quoted × C.Sound.SafeState quoted (R.Checked.closed-goal admitted)))
  run-safe-with fuel admitted with Q.normalise-with C.W.ind fuel 0 (R.Checked.closed-subject admitted) []
  ... | E.stop reason = E.stop reason
  ... | E.done (quoted , execution) with safe-normalization admitted execution
  ... | normal , safe = E.done (quoted , execution , normal , safe)
