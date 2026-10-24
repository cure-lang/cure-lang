------------------------------------------------------------------------
-- Fresh caller slots reconstruct scoped OPEN syntax, independently of
-- actual closing arguments. Identity is not asserted beyond that prefix.
------------------------------------------------------------------------
module Proof.FreshEnvironment where

open import Data.List using (List; []; length)
open import Data.Nat using (ℕ; zero; suc; _<_)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
import Core.BranchOpening as Opening
import Core.ClosureEval as E
import Core.ClosureScope as Scope
import Proof.BranchOpeningFrame as Frame
import Proof.ClosureEvaluation as Meaning
import Proof.DependentScopedAlgebra as Algebra
import Proof.Substitution as Substitution

environment : ℕ → List E.Value
environment size = Opening.environment 0 size []
images : ℕ → List Term
images size = Frame.terms size []
environment-length : ∀ size → length (environment size) ≡ size
environment-length size = trans (Opening.environment-length 0 size []) (Nat.+-identityʳ size)
scoped : ∀ size → Scope.EnvironmentScoped size (environment size)
scoped size = subst (λ depth → Scope.EnvironmentScoped depth (environment size)) (Nat.+-identityʳ size)
  (Frame.environment-scoped size Scope.s[])
denotes : ∀ size → Meaning.Environments size (environment size) (images size)
denotes size = subst (λ depth → Meaning.Environments depth (environment size) (images size)) (Nat.+-identityʳ size)
  (Frame.environment-denotes size Scope.s[] Meaning.d[])
extended-identity : ∀ size k → extSub^ size (Meaning.environment-sub []) k ≡ tm-var k
extended-identity zero k = refl
extended-identity (suc size) zero = refl
extended-identity (suc size) (suc k) = cong (rename wk) (extended-identity size k)
identity-agree : ∀ size → Algebra.Agree size (Meaning.environment-sub (images size)) tm-var
identity-agree size k inside = trans
  (sym (Frame.opening-agree size [] k (subst (λ bound → k < bound) (sym (Nat.+-identityʳ size)) inside)))
  (extended-identity size k)
identity : ∀ {size term} → Scoped size term → substS (Meaning.environment-sub (images size)) term ≡ term
identity {size} {term} scope = trans (Algebra.subst-agree scope (identity-agree size)) (Substitution.substS-idSub term)
source-scope : ∀ {size term} → Scoped size term → Scoped (length (environment size)) term
source-scope {size} {term} scope = subst (λ bound → Scoped bound term) (sym (environment-length size)) scope
