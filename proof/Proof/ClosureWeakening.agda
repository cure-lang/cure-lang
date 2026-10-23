------------------------------------------------------------------------
-- Scoped captured syntax is essential: environment prefix tails differ
-- beyond their actual slots. No arbitrary-body weakening oracle is used.
------------------------------------------------------------------------
module Proof.ClosureWeakening where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
import Core.ClosureEval as E
import Core.ClosureScope as S
import Core.FlatContext as Flat
import Proof.ClosureEvaluation as M
import Proof.DependentScopedAlgebra as A
import Proof.Substitution as Substitution

environment-length : ∀ {d env terms} → M.Environments d env terms → length env ≡ length terms
environment-length M.d[] = refl
environment-length (M.d∷ head rest) = cong suc (environment-length rest)
capture-scope : ∀ {d env terms body} → M.Environments d env terms → Scoped (suc (length env)) body
  → Scoped (suc (length terms)) body
capture-scope {body = body} env scoped = subst (λ n → Scoped (suc n) body) (environment-length env) scoped
prefix-map : ∀ ρ terms k → k < length terms
  → rename ρ (M.environment-sub terms k) ≡ M.environment-sub (renameTerms ρ terms) k
prefix-map ρ [] k ()
prefix-map ρ (term ∷ terms) zero inside = refl
prefix-map ρ (term ∷ terms) (suc k) (s≤s inside) = prefix-map ρ terms k inside
lifted-map : ∀ ρ terms → A.Agree (suc (length terms))
  (Substitution.renameSub (ext ρ) (extSub (M.environment-sub terms)))
  (extSub (M.environment-sub (renameTerms ρ terms)))
lifted-map ρ terms zero inside = refl
lifted-map ρ terms (suc k) (s≤s inside) = trans
  (sym (ext-wk-rename ρ (M.environment-sub terms k))) (cong (rename wk) (prefix-map ρ terms k inside))
rename-body : ∀ ρ terms body → Scoped (suc (length terms)) body
  → rename (ext ρ) (substS (extSub (M.environment-sub terms)) body)
    ≡ substS (extSub (M.environment-sub (renameTerms ρ terms))) body
rename-body ρ terms body scoped = trans (Substitution.rename-subst (ext ρ) (extSub (M.environment-sub terms)) body)
  (A.subst-agree scoped (lifted-map ρ terms))
opening-agree : ∀ terms → A.Agree (suc (length terms)) (extSub (M.environment-sub terms))
  (M.environment-sub (tm-var 0 ∷ renameTerms wk terms))
opening-agree terms zero inside = refl
opening-agree terms (suc k) (s≤s inside) = prefix-map wk terms k inside
open-body : ∀ terms body → Scoped (suc (length terms)) body
  → substS (extSub (M.environment-sub terms)) body
    ≡ substS (M.environment-sub (tm-var 0 ∷ renameTerms wk terms)) body
open-body terms body scoped = A.subst-agree scoped (opening-agree terms)

mutual
  value : ∀ {d v term} → S.ValueScoped d v → M.Denotes d v term → M.Denotes (suc d) v (rename wk term)
  value S.s-type M.d-type = M.d-type
  value S.s-atom-type M.d-atom-type = M.d-atom-type
  value S.s-atom M.d-atom = M.d-atom
  value {d} (S.s-pi domain env body)
    (M.d-pi {g = g} {domain = v} {env = vs} {body = b} {A = ty} {terms = terms} denoted environment) =
    subst (M.Denotes (suc d) (E.v-pi g v vs b))
      (cong (tm-pi g (rename wk ty)) (sym (rename-body wk terms b (capture-scope environment body))))
      (M.d-pi (value domain denoted) (environments env environment))
  value {d} (S.s-lam domain env body)
    (M.d-lam {g = g} {domain = v} {env = vs} {body = b} {A = ty} {terms = terms} denoted environment) =
    subst (M.Denotes (suc d) (E.v-lam g v vs b))
      (cong (tm-lam g (rename wk ty)) (sym (rename-body wk terms b (capture-scope environment body))))
      (M.d-lam (value domain denoted) (environments env environment))
  value (S.s-neutral head) (M.d-neutral denoted) = M.d-neutral (neutrals head denoted)
  environments : ∀ {d env terms} → S.EnvironmentScoped d env → M.Environments d env terms
    → M.Environments (suc d) env (renameTerms wk terms)
  environments S.s[] M.d[] = M.d[]
  environments (S.s∷ head rest) (M.d∷ denoted environment) =
    M.d∷ (value head denoted) (environments rest environment)
  neutrals : ∀ {d head term} → S.NeutralScoped d head → M.Neutrals d head term
    → M.Neutrals (suc d) head (rename wk term)
  neutrals {d} (S.s-var {level} inside) (M.d-var bounded) =
    subst (M.Neutrals (suc d) (E.n-var level)) (cong tm-var (Flat.raise-index d level inside))
      (M.d-var (Nat.<-trans inside (Nat.n<1+n d)))
  neutrals S.s-global M.d-global = M.d-global
  neutrals (S.s-app function argument) (M.d-app denoted actual) = M.d-app
    (neutrals function denoted) (value argument actual)
