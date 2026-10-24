{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Arbitrary-arity fresh opening: scope, denotation and captured-body
-- substitution. Scoped weakening is proved, never an arbitrary callback.
------------------------------------------------------------------------
module Proof.BranchOpening where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.List.Properties using (unfold-reverse)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Reduction using (Signature; _⇝_; _⇝*_; _⇝*ᵇ_; ⇝*-refl; ⇝ᵇ-nil; ⇝ᵇ-cons; ξ-case-brs)
import Core.BranchOpening as Opening
import Core.ClosureEval as E
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Core.FlatContext as Flat
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureWeakening as Weakening
import Proof.ClosureQuotation as Quotation
import Proof.DependentScopedAlgebra as Algebra

open import Proof.BranchOpeningFrame public

module Simulation (sig : Signature) where
  module Quote = Quotation.Simulation sig
  module O = Quote.O
  quotation : ∀ {d arity env captured body quoted} → Scope.EnvironmentScoped d env
    → Scoped (length env + arity) body → Meaning.Environments d env captured
    → Q.Normalizes (arity + d) (Opening.environment d arity env) body quoted
    → _⇝*_ sig (substS (extSub^ arity (Meaning.environment-sub captured)) body) quoted
  quotation {d} {arity} {env} {captured} {body} scope scoped denoted execution =
    O.⇝*-trans (Quote.Eval.equal-path (open-body arity captured body (captured-scope arity denoted scoped)))
      (Quote.normalization (environment-scoped arity scope) (body-scope d arity env scoped)
        (environment-denotes arity scope denoted) execution)

  quotation-at-executable-depth : ∀ {d arity env captured body quoted}
    → Scope.EnvironmentScoped d env → Scoped (length env + arity) body → Meaning.Environments d env captured
    → Q.Normalizes (d + arity) (Opening.environment d arity env) body quoted
    → _⇝*_ sig (substS (extSub^ arity (Meaning.environment-sub captured)) body) quoted
  quotation-at-executable-depth {d} {arity} {env} {body = body} {quoted} scope scoped denoted execution =
    quotation scope scoped denoted
      (subst (λ n → Q.Normalizes n (Opening.environment d arity env) body quoted)
        (Nat.+-comm d arity) execution)

-- Administrative congruence permits identity branch paths. Residual-case
-- readback therefore cannot inherit the old strict no-step contract.
branches-refl : ∀ sig branches → _⇝*ᵇ_ sig branches branches
branches-refl sig [] = ⇝ᵇ-nil
branches-refl sig ((name , arity , body) ∷ rest) = ⇝ᵇ-cons ⇝*-refl (branches-refl sig rest)
case-self-step : ∀ sig scrutinee motive branches
  → _⇝_ sig (tm-case scrutinee motive branches) (tm-case scrutinee motive branches)
case-self-step sig scrutinee motive branches = ξ-case-brs (branches-refl sig branches)
strict-case-irreducibility-impossible : ∀ sig scrutinee motive branches
  → (∀ {endpoint} → _⇝_ sig (tm-case scrutinee motive branches) endpoint → ⊥) → ⊥
strict-case-irreducibility-impossible sig scrutinee motive branches no-step =
  no-step (case-self-step sig scrutinee motive branches)
