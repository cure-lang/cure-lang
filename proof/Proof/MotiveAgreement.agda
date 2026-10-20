------------------------------------------------------------------------
-- Curried index-plus-scrutinee goal agreement for a selected branch.
-- These are substitution equalities and typed reduct theorems, NOT motive
-- well-formedness or a whole-source-case typing/preservation theorem.
------------------------------------------------------------------------
module Proof.MotiveAgreement where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; length; reverse; map)
open import Data.List.Properties using (length-reverse; reverse-involutive)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv; ctor-args; ctor-indices)
open import Core.Reduction
open import Core.Typing using (Ctx; Conversion; surface-field-vars; branch-field-vars)
import Core.LocalFrame as F
open import Proof.LocalFrame using (staged-contraction)
open import Proof.Substitution using (substTerms-reverse)
open import Proof.Progress using (BuiltinCtors; Certified)
open import Proof.Preservation using (ClosedFragmentSig; ReduceConv; CertifiedTyped)
open import Proof.DependentBranch using (find-head)
import Proof.DependentOpening as Opening

apps : Term → List Term → Term
apps function [] = function
apps function (arg ∷ args) = apps (tm-app function arg) args

subst-apps : ∀ σ function args
  → substS σ (apps function args) ≡ apps (substS σ function) (substTermsS σ args)
subst-apps σ function [] = refl
subst-apps σ function (arg ∷ args) = subst-apps σ (tm-app function arg) args

subst-append : ∀ σ xs ys
  → substTermsS σ (xs ++ ys) ≡ substTermsS σ xs ++ substTermsS σ ys
subst-append σ [] ys = refl
subst-append σ (x ∷ xs) ys = cong (substS σ x ∷_) (subst-append σ xs ys)

staged-indices : ∀ ps fields ar indices → length fields ≡ ar
  → substTermsS (argsSub (reverse fields)) (map (F.specializeParameters ar ps) indices)
      ≡ F.instantiateResults ps fields indices
staged-indices ps fields ar [] size = refl
staged-indices ps fields ar (index ∷ indices) size =
  cong₂ _∷_
    (trans (cong (λ k → substArgs fields (F.specializeParameters k ps index)) (sym size))
      (staged-contraction ps fields index))
    (staged-indices ps fields ar indices size)

module Agreement (base : IndEnv) (sig : Signature) (conv : Conversion) (registry : IndEnv)
  (closed : ClosedFragmentSig base sig) (rc : ReduceConv sig conv)
  (typed : CertifiedTyped base sig conv) (bc : BuiltinCtors base) (cert : Certified sig) where
  module O = Opening.Typed base sig conv registry closed rc typed bc cert
  module L = O.L
  module P = O.P
  open Core.Typing.Typing base sig conv

  arity : ∀ {n} {Γ : Ctx n} {name ps fields} → L.Application Γ name ps fields → ℕ
  arity app = length (ctor-args (L.Application.ctor app))

  fresh-indices : ∀ {n} {Γ : Ctx n} {name ps fields}
    → L.Application Γ name ps fields → List Term
  fresh-indices {ps = ps} app =
    map (F.specializeParameters (arity app) ps) (ctor-indices (L.Application.ctor app))

  branch-goal : ∀ {n} {Γ : Ctx n} {name ps fields}
    → L.Application Γ name ps fields → Term → Term
  branch-goal {name = name} app motive =
    apps (shift (arity app) 0 motive)
      (fresh-indices app ++ tm-ctor name (surface-field-vars (arity app)) ∷ [])

  result-goal : ∀ {n} {Γ : Ctx n} {name ps fields}
    → L.Application Γ name ps fields → Term → Term
  result-goal {name = name} {ps = ps} {fields = fields} app motive =
    apps motive (F.instantiateResults ps fields (ctor-indices (L.Application.ctor app))
      ++ tm-ctor name fields ∷ [])

  fields-agree : ∀ {n} {Γ : Ctx n} {name ps fields} (app : L.Application Γ name ps fields)
    → substTermsS (argsSub (reverse fields)) (surface-field-vars (arity app)) ≡ fields
  fields-agree {fields = fields} app =
    trans (substTerms-reverse (argsSub (reverse fields)) (branch-field-vars (arity app)))
      (trans (cong reverse (P.substArgs-field-vars {args = reverse fields} (ctor-args (L.Application.ctor app))
        (trans (length-reverse fields) (L.T.arguments-length (L.Application.fields app)))))
        (reverse-involutive fields))

  goal-agreement : ∀ {n} {Γ : Ctx n} {name ps fields}
    → (app : L.Application Γ name ps fields) → ∀ motive
    → substArgs fields (branch-goal app motive) ≡ result-goal app motive
  goal-agreement {name = name} {ps = ps} {fields = fields} app motive =
    trans (subst-apps σ (shift (arity app) 0 motive)
      (fresh-indices app ++ tm-ctor name (surface-field-vars (arity app)) ∷ []))
      (cong₂ apps
        (P.substArgs-motive {args = reverse fields} (ctor-args (L.Application.ctor app)) motive
          (trans (length-reverse fields) (L.T.arguments-length (L.Application.fields app))))
        (trans (subst-append σ (fresh-indices app)
          (tm-ctor name (surface-field-vars (arity app)) ∷ []))
          (cong₂ _++_
            (staged-indices ps fields (arity app) (ctor-indices (L.Application.ctor app))
              (L.T.arguments-length (L.Application.fields app)))
            (cong (λ args → tm-ctor name args ∷ []) (fields-agree app)))))
    where σ = argsSub (reverse fields)

  -- The branch-body premise is in the typed fresh caller context. No
  -- assumption claims that arbitrary motives are well-formed functions.
  contract-at-motive : ∀ {n} {Γ : Ctx n} {name ps fields body}
    → (app : L.Application Γ name ps fields) → (motive : Term)
    → O.branch-context app ⊢ body ⇐ branch-goal app motive
    → Γ ⊢ substArgs fields body ⇐ result-goal app motive
  contract-at-motive {Γ = Γ} {fields = fields} {body = body} app motive checked =
    subst (λ goal → Γ ⊢ substArgs fields body ⇐ goal)
      (goal-agreement app motive) (O.contract-branch app checked)

  selected-step : ∀ {n} {Γ : Ctx n} {name ps fields}
    → (app : L.Application Γ name ps fields) → ∀ body motive tail
    → _⇝_ sig
        (tm-case (tm-ctor name fields) motive ((name , arity app , body) ∷ tail))
        (substArgs fields body)
  selected-step {name = name} app body motive tail =
    ι (find-head name (arity app) body tail) (L.T.arguments-length (L.Application.fields app))
