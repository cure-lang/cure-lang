------------------------------------------------------------------------
-- Stability of LOCAL declaration instantiation. The scope premise is
-- essential: declaration variables refer to preceding fields/parameters,
-- not to the unrelated ambient typing context.
------------------------------------------------------------------------
module Proof.LocalFrame where

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Properties using (length-reverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Core.Syntax
open import Core.LocalFrame
open import Core.Reduction using (substArgs)
open import Proof.Substitution
  using (rename-prefix; subst-prefix; rename-scoped; substS-scoped;
         ext^-fix; extSub^-fix; subst-rename; subst-compose; substCompose; substS-idSub)

rename-local : ∀ {locals ty} → Scoped (length locals) ty → ∀ ρ
  → rename ρ (instantiatePrefix locals ty)
    ≡ instantiatePrefix (renameTerms ρ locals) ty
rename-local {locals} {ty} scoped ρ =
  trans (rename-prefix ρ locals ty)
    (cong (instantiatePrefix (renameTerms ρ locals))
      (rename-scoped scoped (ext^-fix (length locals) ρ)))

subst-local : ∀ {locals ty} → Scoped (length locals) ty → ∀ σ
  → substS σ (instantiatePrefix locals ty)
    ≡ instantiatePrefix (substTermsS σ locals) ty
subst-local {locals} {ty} scoped σ =
  trans (subst-prefix σ locals ty)
    (cong (instantiatePrefix (substTermsS σ locals))
      (substS-scoped scoped (extSub^-fix (length locals) σ)))

push-undoes-wk : ∀ arg σ T
  → substS (push arg σ) (rename wk T) ≡ substS σ T
push-undoes-wk arg σ T =
  trans (subst-rename (push arg σ) wk T)
    (cong (λ τ → substS τ T) (funext (λ i → refl)))

prefix-extended : ∀ xs σ i
  → substCompose (prefix xs identity) (extSub^ (length xs) σ) i ≡ prefix xs σ i
prefix-extended [] σ i = substS-idSub (σ i)
prefix-extended (x ∷ xs) σ zero = refl
prefix-extended (x ∷ xs) σ (suc i) =
  trans (push-undoes-wk x (prefix xs identity) (extSub^ (length xs) σ i))
    (prefix-extended xs σ i)

-- Arbitrary bodies and OPEN caller parameters: first specialise the
-- parameters beneath the fields, then contract the fields simultaneously.
-- This is exact equality, including nested lambda/case capture avoidance.
staged-contraction : ∀ parameters fields body
  → substArgs fields (specializeParameters (length fields) parameters body)
      ≡ instantiateResult parameters fields body
staged-contraction parameters fields body =
  trans (cong (λ ar → substArgs fields (specializeParameters ar parameters body))
    (sym (length-reverse fields)))
    (trans (cong (λ τ → substS τ (specializeParameters (length xs) parameters body))
      (sym (funext (prefix-args 0 xs))))
      (trans (subst-compose (prefix xs identity) (extSub^ (length xs) σ) body)
        (trans (cong (λ τ → substS τ body) (funext (prefix-extended xs σ)))
          (cong (λ τ → substS τ body) (sym (funext (advance-reverse fields σ)))))))
  where
    xs = reverse fields
    σ = advance parameters identity
