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

reverse-snoc : ∀ {A : Set} (xs : List A) x → reverse (xs ++ x ∷ []) ≡ x ∷ reverse xs
reverse-snoc [] x = refl
reverse-snoc (y ∷ ys) x = trans (unfold-reverse y (ys ++ x ∷ []))
  (trans (cong (_++ y ∷ []) (reverse-snoc ys x)) (cong (x ∷_) (sym (unfold-reverse y ys))))
frame-agrees : ∀ depth arity env
  → Opening.environment depth arity env ≡ reverse (Opening.forward depth arity) ++ env
frame-agrees depth zero env = refl
frame-agrees depth (suc arity) env = trans
  (cong₂ _∷_ (cong Opening.fresh (Nat.+-comm arity depth)) (frame-agrees depth arity env))
  (sym (cong (_++ env) (reverse-snoc (Opening.forward depth arity) (Opening.fresh (depth + arity)))))
depth-agrees : ∀ depth arity → arity + depth ≡ depth + arity
depth-agrees depth arity = Nat.+-comm arity depth

terms : ℕ → List Term → List Term
terms zero captured = captured
terms (suc arity) captured = tm-var 0 ∷ renameTerms wk (terms arity captured)
rename-length : ∀ ρ xs → length (renameTerms ρ xs) ≡ length xs
rename-length ρ [] = refl
rename-length ρ (x ∷ xs) = cong suc (rename-length ρ xs)
terms-length : ∀ arity captured → length (terms arity captured) ≡ arity + length captured
terms-length zero captured = refl
terms-length (suc arity) captured = cong suc
  (trans (rename-length wk (terms arity captured)) (terms-length arity captured))

environment-scoped : ∀ {d env} arity → Scope.EnvironmentScoped d env
  → Scope.EnvironmentScoped (arity + d) (Opening.environment d arity env)
environment-scoped zero scope = scope
environment-scoped {d} (suc arity) scope = Scope.s∷
  (Scope.s-neutral (Scope.s-var (Nat.n<1+n (arity + d))))
  (Scope.raise-environment (environment-scoped arity scope))
environment-denotes : ∀ {d env captured} arity → Scope.EnvironmentScoped d env
  → Meaning.Environments d env captured
  → Meaning.Environments (arity + d) (Opening.environment d arity env) (terms arity captured)
environment-denotes zero scope denoted = denoted
environment-denotes {d} (suc arity) scope denoted = Meaning.d∷
  (Meaning.flat-denotation (Flat.fresh (arity + d)))
  (Weakening.environments (environment-scoped arity scope) (environment-denotes arity scope denoted))

opening-agree : ∀ arity captured → Algebra.Agree (arity + length captured)
  (extSub^ arity (Meaning.environment-sub captured)) (Meaning.environment-sub (terms arity captured))
opening-agree zero captured k inside = refl
opening-agree (suc arity) captured zero inside = refl
opening-agree (suc arity) captured (suc k) (s≤s inside) = trans
  (cong (rename wk) (opening-agree arity captured k inside))
  (Weakening.prefix-map wk (terms arity captured) k
    (subst (λ n → k < n) (sym (terms-length arity captured)) inside))
open-body : ∀ arity captured body → Scoped (arity + length captured) body
  → substS (extSub^ arity (Meaning.environment-sub captured)) body
    ≡ substS (Meaning.environment-sub (terms arity captured)) body
open-body arity captured body scope = Algebra.subst-agree scope (opening-agree arity captured)
captured-scope : ∀ {d env captured body} arity → Meaning.Environments d env captured
  → Scoped (length env + arity) body → Scoped (arity + length captured) body
captured-scope {captured = captured} {body} arity denoted scope =
  subst (λ n → Scoped n body)
    (trans (cong (_+ arity) (Weakening.environment-length denoted)) (Nat.+-comm (length captured) arity)) scope
body-scope : ∀ depth arity env {body} → Scoped (length env + arity) body
  → Scoped (length (Opening.environment depth arity env)) body
body-scope depth arity env {body} scope = subst (λ n → Scoped n body)
  (trans (Nat.+-comm (length env) arity) (sym (Opening.environment-length depth arity env))) scope

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
