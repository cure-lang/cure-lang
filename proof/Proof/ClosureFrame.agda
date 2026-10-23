------------------------------------------------------------------------
-- Pure branch/caller substitution algebra, independent of evaluation,
-- scope and quotation. No arbitrary-body substitution oracle is assumed.
------------------------------------------------------------------------
module Proof.ClosureFrame where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.List.Properties using (length-reverse)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Core.Syntax
open import Core.Reduction using (argsSub; substArgs)
import Core.LocalFrame as F
import Proof.Substitution as S

environment-sub : List Term → Sub
environment-sub terms = F.prefix terms F.identity

consume : ∀ xs σ k → substS (argsSub xs) (extSub^ (length xs) σ k) ≡ F.prefix xs σ k
consume [] σ k = S.substS-idSub (σ k)
consume (x ∷ xs) σ zero = refl
consume (x ∷ xs) σ (suc k) =
  trans (S.substS-argsSub-wk x xs (extSub^ (length xs) σ k)) (consume xs σ k)

branch-environment : ∀ args terms body
  → substArgs args (substS (extSub^ (length args) (environment-sub terms)) body)
    ≡ substS (environment-sub (reverse args ++ terms)) body
branch-environment args terms body =
  trans (cong (λ n → substS (argsSub (reverse args))
    (substS (extSub^ n (environment-sub terms)) body)) (sym (length-reverse args)))
    (trans (S.subst-compose (argsSub (reverse args))
      (extSub^ (length (reverse args)) (environment-sub terms)) body)
      (cong (λ σ → substS σ body) (funext (λ k →
        trans (consume (reverse args) (environment-sub terms) k)
          (sym (F.prefix-append (reverse args) terms F.identity k))))))
