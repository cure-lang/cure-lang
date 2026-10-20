------------------------------------------------------------------------
-- Binder-aware algebra for native dependent transport. These are exact
-- syntax equalities, not an inference/checking substitution theorem.
-- Local declarations stay fixed; actual caller arguments are transformed.
------------------------------------------------------------------------
module Proof.DependentNaturality where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; _++_; length; reverse; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Core.Syntax
open import Core.Signature using (Telescope)
open import Core.Grade using (unrestricted)
open import Core.DependentTyping using (piTele)
import Core.LocalFrame as F
import Proof.LocalFrame as Local
open import Proof.Substitution
  using (renameSub; rename-subst; renameSub-extSub-eq;
         substCompose; subst-compose; extSub-compose;
         renameTerms-reverse; substTerms-reverse)

ext-suc : ∀ k ρ → ext^ k (ext ρ) ≡ ext^ (suc k) ρ
ext-suc zero ρ = refl
ext-suc (suc k) ρ = cong ext (ext-suc k ρ)
extSub-suc : ∀ k σ → extSub^ k (extSub σ) ≡ extSub^ (suc k) σ
extSub-suc zero σ = refl
extSub-suc (suc k) σ = cong extSub (extSub-suc k σ)

abstract
  -- These telescope laws need no scoping assumption: the complete local
  -- substitution is mapped, including its tail. Canonical parameter
  -- frames require the separate scope-aware laws below.
  rename-piTele : ∀ ρ σ tele body
    → rename ρ (piTele σ tele body)
      ≡ piTele (renameSub ρ σ) tele (rename (ext^ (length tele) ρ) body)
  rename-piTele ρ σ [] body = refl
  rename-piTele ρ σ ((name , T) ∷ tele) body =
    cong₂ (tm-pi unrestricted) (rename-subst ρ σ T)
      (trans (rename-piTele (ext ρ) (extSub σ) tele body)
        (cong₂ (λ τ b → piTele τ tele b) (renameSub-extSub-eq ρ σ)
          (cong (λ r → rename r body) (ext-suc (length tele) ρ))))

  subst-piTele : ∀ τ σ tele body
    → substS τ (piTele σ tele body)
      ≡ piTele (substCompose τ σ) tele (substS (extSub^ (length tele) τ) body)
  subst-piTele τ σ [] body = refl
  subst-piTele τ σ ((name , T) ∷ tele) body =
    cong₂ (tm-pi unrestricted) (subst-compose τ σ T)
      (trans (subst-piTele (extSub τ) (extSub σ) tele body)
        (cong₂ (λ ρ b → piTele ρ tele b) (funext (extSub-compose τ σ))
          (cong (λ ρ → substS ρ body) (extSub-suc (length tele) τ))))

  rename-append : ∀ ρ xs ys
    → renameTerms ρ (xs ++ ys) ≡ renameTerms ρ xs ++ renameTerms ρ ys
  rename-append ρ [] ys = refl
  rename-append ρ (x ∷ xs) ys = cong (rename ρ x ∷_) (rename-append ρ xs ys)
  subst-append : ∀ σ xs ys
    → substTermsS σ (xs ++ ys) ≡ substTermsS σ xs ++ substTermsS σ ys
  subst-append σ [] ys = refl
  subst-append σ (x ∷ xs) ys = cong (substS σ x ∷_) (subst-append σ xs ys)

  rename-frame : ∀ ρ ps fields
    → renameTerms ρ (reverse fields ++ reverse ps)
      ≡ reverse (renameTerms ρ fields) ++ reverse (renameTerms ρ ps)
  rename-frame ρ ps fields = trans (rename-append ρ (reverse fields) (reverse ps))
    (cong₂ _++_ (renameTerms-reverse ρ fields) (renameTerms-reverse ρ ps))
  subst-frame : ∀ σ ps fields
    → substTermsS σ (reverse fields ++ reverse ps)
      ≡ reverse (substTermsS σ fields) ++ reverse (substTermsS σ ps)
  subst-frame σ ps fields = trans (subst-append σ (reverse fields) (reverse ps))
    (cong₂ _++_ (substTerms-reverse σ fields) (substTerms-reverse σ ps))

  rename-result : ∀ ρ ps fields t
    → Scoped (length (reverse fields ++ reverse ps)) t
    → rename ρ (F.instantiateResult ps fields t)
      ≡ F.instantiateResult (renameTerms ρ ps) (renameTerms ρ fields) t
  rename-result ρ ps fields t scoped =
    trans (cong (rename ρ) (F.result-agree ps fields t))
      (trans (Local.rename-local {locals = reverse fields ++ reverse ps} {ty = t} scoped ρ)
        (trans (cong (λ locals → F.instantiatePrefix locals t) (rename-frame ρ ps fields))
          (sym (F.result-agree (renameTerms ρ ps) (renameTerms ρ fields) t))))

  subst-result : ∀ σ ps fields t
    → Scoped (length (reverse fields ++ reverse ps)) t
    → substS σ (F.instantiateResult ps fields t)
      ≡ F.instantiateResult (substTermsS σ ps) (substTermsS σ fields) t
  subst-result σ ps fields t scoped =
    trans (cong (substS σ) (F.result-agree ps fields t))
      (trans (Local.subst-local {locals = reverse fields ++ reverse ps} {ty = t} scoped σ)
        (trans (cong (λ locals → F.instantiatePrefix locals t) (subst-frame σ ps fields))
          (sym (F.result-agree (substTermsS σ ps) (substTermsS σ fields) t))))

  rename-results : ∀ ρ ps fields ts
    → ScopedTerms (length (reverse fields ++ reverse ps)) ts
    → renameTerms ρ (F.instantiateResults ps fields ts)
      ≡ F.instantiateResults (renameTerms ρ ps) (renameTerms ρ fields) ts
  rename-results ρ ps fields [] st[] = refl
  rename-results ρ ps fields (t ∷ ts) (st∷ scoped scopes) =
    cong₂ _∷_ (rename-result ρ ps fields t scoped) (rename-results ρ ps fields ts scopes)

  subst-results : ∀ σ ps fields ts
    → ScopedTerms (length (reverse fields ++ reverse ps)) ts
    → substTermsS σ (F.instantiateResults ps fields ts)
      ≡ F.instantiateResults (substTermsS σ ps) (substTermsS σ fields) ts
  subst-results σ ps fields [] st[] = refl
  subst-results σ ps fields (t ∷ ts) (st∷ scoped scopes) =
    cong₂ _∷_ (subst-result σ ps fields t scoped) (subst-results σ ps fields ts scopes)
