{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Equal bounded model normal forms -> native common reduct/conversion.
-- Positive soundness only; never a non-conversion or eta completeness claim.
------------------------------------------------------------------------
module Proof.NormalFormConversion where

open import Data.List using ([]; length)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Data.Product using (_×_; _,_)
open import Core.Syntax
open import Core.Typing using (Conversion)
open import Core.Reduction using (Signature; _⇝*_)
open import Core.LiteralExpansion using (expand)
import Core.CheckedAdmission as Admission
import Core.ClosureScope as Scope
import Core.NormalFormComparison as Compare
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quotation
import Proof.Substitution as Substitution

module Common (sig : Signature) where
  module Model = Quotation.Simulation sig
  joined : ∀ {depth env terms left right} → Scope.EnvironmentScoped depth env
    → Scoped (length env) left → Scoped (length env) right → Meaning.Environments depth env terms
    → (equal : Compare.EqualNormal depth env left right)
    → _⇝*_ sig (substS (Meaning.environment-sub terms) left) (Compare.EqualNormal.common equal)
      × _⇝*_ sig (substS (Meaning.environment-sub terms) right) (Compare.EqualNormal.common equal)
  joined env-scope left-scope right-scope env equal =
    Model.normalization env-scope left-scope env (Compare.EqualNormal.left-execution equal) ,
    Model.normalization env-scope right-scope env (Compare.EqualNormal.right-execution equal)

module Sound {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module C = Admission.Checked source-checked
  module Paths = Common C.W.sig
  conversion : ∀ {depth env terms left right} → Scope.EnvironmentScoped depth env
    → Scoped (length env) left → Scoped (length env) right → Meaning.Environments depth env terms
    → Compare.EqualNormal depth env left right
    → Conversion._≈_ C.W.M.conversion
      (substS (Meaning.environment-sub terms) left) (substS (Meaning.environment-sub terms) right)
  conversion env-scope left-scope right-scope env equal
    with Paths.joined env-scope left-scope right-scope env equal
  ... | left-path , right-path = expand (Compare.EqualNormal.common equal) ,
    C.W.M.E.expand-star left-path , C.W.M.E.expand-star right-path

  closed-conversion : ∀ {left right} → Scoped 0 left → Scoped 0 right
    → Compare.EqualNormal 0 [] left right → Conversion._≈_ C.W.M.conversion left right
  closed-conversion {left} {right} left-scope right-scope equal =
    subst₂ (Conversion._≈_ C.W.M.conversion)
      (Substitution.substS-idSub left) (Substitution.substS-idSub right)
      (conversion Scope.s[] left-scope right-scope Meaning.d[] equal)
