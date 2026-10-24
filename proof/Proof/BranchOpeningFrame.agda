------------------------------------------------------------------------
-- Arbitrary-arity fresh opening: scope, denotation and captured-body
-- substitution. Scoped weakening is proved, never an arbitrary callback.
------------------------------------------------------------------------
module Proof.BranchOpeningFrame where

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
import Core.FlatContext as Flat
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureWeakening as Weakening
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

