{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Positive neutral-case readback refinement. Captured source scope and
-- one denoting caller environment are premises, not typing oracles.
------------------------------------------------------------------------
module Proof.NeutralCase where

open import Data.List using ([]; _∷_; length)
open import Data.Nat using (ℕ; _+_)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)
open import Core.Syntax
open import Core.Reduction using (Signature; _⇝*_; _⇝*ᵇ_; ⇝ᵇ-nil; ⇝ᵇ-cons)
import Core.NeutralCase as Case
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Core.ResidualNormal as Normal
import Proof.ResidualNormal as Residual
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quote
import Proof.BranchOpening as Opening
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller

branches-scoped : ∀ {d env branches results} → Case.BranchesRead d env branches results → ScopedBranches d results
branches-scoped Case.b[] = sb[]
branches-scoped {d} (Case.b∷ {ar = ar} {quoted = quoted} head tail) = sb∷
  (sbranch (subst (λ n → Scoped n quoted) (Nat.+-comm ar d)
    (Q.quoted-scoped (Q.Normalizes.quoted head)))) (branches-scoped tail)
scoped : ∀ {d env s m branches cap} → (out : Case.Readback d env s m branches cap) → Scoped d (Case.Readback.term out)
scoped out = sc-case (Q.neutral-scoped (Case.Readback.head-quoted out))
  (Q.quoted-scoped (Q.Normalizes.quoted (Case.Readback.motive-execution out)))
  (branches-scoped (Case.Readback.branches-read out))
branches-normal : ∀ {d env branches results} → Case.BranchesRead d env branches results
  → Normal.Branches Residual.no-delta results
branches-normal Case.b[] = Normal.nb[]
branches-normal (Case.b∷ head tail) = Normal.nb∷
  (Residual.strict-embedding (Q.quoted-normal (Q.Normalizes.quoted head))) (branches-normal tail)
normal : ∀ {d env s m branches cap} (out : Case.Readback d env s m branches cap)
  → Normal.Normal Residual.no-delta (Case.Readback.term out)
normal out = Normal.nf-neutral (Normal.ne-case
  (Residual.strict-neutral (Q.neutral-normal (Case.Readback.head-quoted out)))
  (Residual.strict-embedding (Q.quoted-normal (Q.Normalizes.quoted (Case.Readback.motive-execution out))))
  (branches-normal (Case.Readback.branches-read out)))

module Simulation (sig : Signature) where
  module Quotation = Quote.Simulation sig
  module Eval = Quotation.Eval
  module O = Quotation.O
  module Branch = Opening.Simulation sig
  branches-path : ∀ {d env captured branches results}
    → Scope.EnvironmentScoped d env → ScopedBranches (length env) branches → Meaning.Environments d env captured
    → Case.BranchesRead d env branches results
    → _⇝*ᵇ_ sig (substBranchesS (Meaning.environment-sub captured) branches) results
  branches-path scope sb[] env Case.b[] = ⇝ᵇ-nil
  branches-path scope (sb∷ (sbranch body) rest) env (Case.b∷ head tail) =
    ⇝ᵇ-cons (Branch.quotation scope body env head) (branches-path scope rest env tail)

  quotation : ∀ {d env captured s m branches} (cap : Case.Captured env s)
    → (out : Case.Readback d env s m branches cap)
    → Scope.EnvironmentScoped d env → Scoped (length env) (tm-case s m branches)
    → Meaning.Environments d env captured
    → _⇝*_ sig (substS (Meaning.environment-sub captured) (tm-case s m branches)) (Case.Readback.term out)
  quotation cap out scope (sc-case scrutinee motive branches) env
    with Eval.evaluate env (Case.Captured.evaluated cap)
      | Scope.evaluate-scoped scope scrutinee (Case.Captured.evaluated cap)
  ... | result , Meaning.d-neutral denoted , evaluated | Scope.s-neutral head-scope =
    O.⇝*-trans (O.⇝*-case evaluated)
      (O.⇝*-trans (O.⇝*-case (Quotation.neutral-quotation head-scope denoted (Case.Readback.head-quoted out)))
        (O.⇝*-trans (O.⇝*-case-motive
          (Quotation.normalization scope motive env (Case.Readback.motive-execution out)))
          (O.⇝*-case-brs (branches-path scope branches env (Case.Readback.branches-read out)))))

module Safe {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  module C = R.C
  module Model = Simulation C.W.sig
  safe-readback : ∀ {request env captured s m branches cap} (admitted : R.Checked request)
    → (out : Case.Readback 0 env s m branches cap)
    → R.Checked.closed-subject admitted ≡ substS (Meaning.environment-sub captured) (tm-case s m branches)
    → Scope.EnvironmentScoped 0 env → Scoped (length env) (tm-case s m branches)
    → Meaning.Environments 0 env captured
    → C.Sound.SafeState (Case.Readback.term out) (R.Checked.closed-goal admitted)
  safe-readback admitted out shape scope scoped env = R.Checked.trace-safe admitted
    (Model.O.⇝*-source (sym shape) (Model.quotation _ out scope scoped env))
