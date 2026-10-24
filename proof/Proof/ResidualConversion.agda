{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Positive common residual readback yields native conversion, even if
-- that endpoint has administrative steps or certified delta redexes.
------------------------------------------------------------------------
module Proof.ResidualConversion where

open import Data.List using ([]; length)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Core.Syntax
open import Core.Typing using (Conversion)
open import Core.Reduction using (Signature; _⇝*_)
open import Core.LiteralExpansion using (expand)
import Core.CheckedAdmission as Admission
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Core.ResidualComparison as Compare
import Core.NormalFormComparison as Strict
import Core.ResidualNormal as Normal
import Proof.ResidualNormal as Residual
import Proof.ResidualQuotation as Readback
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quotation
import Proof.Substitution as Substitution

normal : ∀ {depth env left right} (equal : Compare.EqualResidual depth env left right)
  → Normal.Normal Residual.no-delta (Compare.EqualResidual.common equal)
normal equal = Readback.normal (Q.ResidualNormalizes.quoted (Compare.EqualResidual.left-execution equal))
from-strict : ∀ {depth env left right} → Strict.EqualNormal depth env left right
  → Compare.EqualResidual depth env left right
from-strict equal = record
  { common = Strict.EqualNormal.common equal
  ; left-execution = Readback.enable-normalization (Strict.EqualNormal.left-execution equal)
  ; right-execution = Readback.enable-normalization (Strict.EqualNormal.right-execution equal) }

module Common (sig : Signature) where
  module Model = Quotation.Simulation sig
  joined : ∀ {depth env terms left right} → Scope.EnvironmentScoped depth env
    → Scoped (length env) left → Scoped (length env) right → Meaning.Environments depth env terms
    → (equal : Compare.EqualResidual depth env left right)
    → _⇝*_ sig (substS (Meaning.environment-sub terms) left) (Compare.EqualResidual.common equal)
      × _⇝*_ sig (substS (Meaning.environment-sub terms) right) (Compare.EqualResidual.common equal)
  joined env-scope left-scope right-scope env equal =
    Model.residual-normalization env-scope left-scope env (Compare.EqualResidual.left-execution equal) ,
    Model.residual-normalization env-scope right-scope env (Compare.EqualResidual.right-execution equal)

module Sound {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module C = Admission.Checked source-checked
  module Paths = Common C.W.sig
  conversion : ∀ {depth env terms left right} → Scope.EnvironmentScoped depth env
    → Scoped (length env) left → Scoped (length env) right → Meaning.Environments depth env terms
    → Compare.EqualResidual depth env left right
    → Conversion._≈_ C.W.M.conversion
      (substS (Meaning.environment-sub terms) left) (substS (Meaning.environment-sub terms) right)
  conversion env-scope left-scope right-scope env equal
    with Paths.joined env-scope left-scope right-scope env equal
  ... | left-path , right-path = expand (Compare.EqualResidual.common equal) ,
    C.W.M.E.expand-star left-path , C.W.M.E.expand-star right-path
  closed-conversion : ∀ {left right} → Scoped 0 left → Scoped 0 right
    → Compare.EqualResidual 0 [] left right → Conversion._≈_ C.W.M.conversion left right
  closed-conversion {left} {right} left-scope right-scope equal =
    subst₂ (Conversion._≈_ C.W.M.conversion)
      (Substitution.substS-idSub left) (Substitution.substS-idSub right)
      (conversion Scope.s[] left-scope right-scope Meaning.d[] equal)
