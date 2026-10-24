{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Positive recursive residual readback, not strict irreducibility,
-- executable completeness or semantic termination of certified bodies.
------------------------------------------------------------------------
module Proof.ResidualQuotation where

open import Data.List using (length; _∷_)
import Data.Bool
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Core.Syntax
import Core.ClosureQuote as Q
import Core.ClosureScope as Scope
import Core.NeutralCase as Case
import Core.ResidualNormal as Normal
import Proof.ResidualNormal as Residual
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quote
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller

mutual
  normal : ∀ {residual d value term} → Q.QuotedIn residual d value term → Normal.Normal Residual.no-delta term
  normal Q.q-type = Normal.nf-type
  normal Q.q-atom-type = Normal.nf-atom-type
  normal Q.q-atom = Normal.nf-atom
  normal (Q.q-ctor fields) = Normal.nf-ctor (spine-normal fields)
  normal (Q.q-data params indices) = Normal.nf-data (spine-normal params) (spine-normal indices)
  normal (Q.q-pi evaluated domain body) = Normal.nf-pi (normal domain) (normal body)
  normal (Q.q-lam evaluated domain body) = Normal.nf-lam (normal domain) (normal body)
  normal (Q.q-neutral head) = Normal.nf-neutral (neutral-normal head)
  neutral-normal : ∀ {residual d head term} → Q.NeutralQuotedIn residual d head term → Normal.Residual Residual.no-delta term
  neutral-normal (Q.q-var inside) = Normal.ne-var
  neutral-normal Q.q-global = Normal.ne-global refl
  neutral-normal (Q.q-app function argument) = Normal.ne-app (neutral-normal function) (normal argument)
  neutral-normal (Q.q-case allowed head evaluated motive branches) =
    Normal.ne-case (neutral-normal head) (normal motive) (branches-normal branches)
  spine-normal : ∀ {residual d values terms} → Q.SpineQuotedIn residual d values terms → Normal.Normals Residual.no-delta terms
  spine-normal Q.q[] = Normal.nf[]
  spine-normal (Q.q∷ head tail) = Normal.nf∷ (normal head) (spine-normal tail)
  branches-normal : ∀ {residual d env source results} → Q.BranchesQuotedIn residual d env source results
    → Normal.Branches Residual.no-delta results
  branches-normal Q.qb[] = Normal.nb[]
  branches-normal (Q.qb∷ evaluated head tail) = Normal.nb∷ (normal head) (branches-normal tail)

metadata-preserved : ∀ {residual d env source results} → Q.BranchesQuotedIn residual d env source results
  → Case.metadata source ≡ Case.metadata results
metadata-preserved Q.qb[] = refl
metadata-preserved (Q.qb∷ {name = name} {ar = ar} evaluated head tail) =
  cong ((name , ar) ∷_) (metadata-preserved tail)

-- Existing strict evidence embeds constructively; no equality of budgets
-- or claim about which worker finishes first is required.
mutual
  enable : ∀ {d value term} → Q.Quoted d value term → Q.QuotedIn Data.Bool.true d value term
  enable Q.q-type = Q.q-type
  enable Q.q-atom-type = Q.q-atom-type
  enable Q.q-atom = Q.q-atom
  enable (Q.q-ctor fields) = Q.q-ctor (enable-spine fields)
  enable (Q.q-data params indices) = Q.q-data (enable-spine params) (enable-spine indices)
  enable (Q.q-pi evaluated domain body) = Q.q-pi evaluated (enable domain) (enable body)
  enable (Q.q-lam evaluated domain body) = Q.q-lam evaluated (enable domain) (enable body)
  enable (Q.q-neutral head) = Q.q-neutral (enable-neutral head)
  enable-neutral : ∀ {d head term} → Q.NeutralQuoted d head term → Q.NeutralQuotedIn Data.Bool.true d head term
  enable-neutral (Q.q-var inside) = Q.q-var inside
  enable-neutral Q.q-global = Q.q-global
  enable-neutral (Q.q-app head argument) = Q.q-app (enable-neutral head) (enable argument)
  enable-neutral (Q.q-case () head evaluated motive branches)
  enable-spine : ∀ {d values terms} → Q.SpineQuoted d values terms → Q.SpineQuotedIn Data.Bool.true d values terms
  enable-spine Q.q[] = Q.q[]
  enable-spine (Q.q∷ head tail) = Q.q∷ (enable head) (enable-spine tail)

enable-normalization : ∀ {d env source result} → Q.Normalizes d env source result → Q.ResidualNormalizes d env source result
enable-normalization execution = Q.residual-normalized (Q.Normalizes.value execution)
  (Q.Normalizes.evaluated execution) (enable (Q.Normalizes.quoted execution))

module Safe {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  module C = R.C
  module Model = Quote.Simulation C.W.sig
  safe-normalization : ∀ {request env captured program result} (admitted : R.Checked request)
    → Q.ResidualNormalizes 0 env program result
    → R.Checked.closed-subject admitted ≡ substS (Meaning.environment-sub captured) program
    → Scope.EnvironmentScoped 0 env → Scoped (length env) program → Meaning.Environments 0 env captured
    → C.Sound.SafeState result (R.Checked.closed-goal admitted)
  safe-normalization admitted execution shape scope scoped env = R.Checked.trace-safe admitted
    (Model.O.⇝*-source (sym shape) (Model.residual-normalization scope scoped env execution))
