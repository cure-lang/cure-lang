------------------------------------------------------------------------
-- Fields arrive in declaration order and are pushed most-recent-first,
-- as in Kernel.do_spine/check_ctor_app_rec and exact-arity branch frames.
-- Parameter filtering and missing erased slots are NOT modelled here.
------------------------------------------------------------------------
module Core.LocalFrame where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length; reverse; map)
open import Data.List.Properties using (unfold-reverse; length-reverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Core.Syntax
open import Core.Reduction using (argsSub; argsSub-go)

identity : Sub
identity = tm-var

push : Term → Sub → Sub
push x σ zero = x
push x σ (suc k) = σ k

prefix : List Term → Sub → Sub
prefix [] σ = σ
prefix (x ∷ xs) σ = push x (prefix xs σ)

-- Unlike extSub, push does not rename argument terms. Arguments already
-- live in the caller's context; they must not capture one another.
advance : List Term → Sub → Sub
advance [] σ = σ
advance (x ∷ xs) σ = advance xs (push x σ)

prefix-append : ∀ xs ys σ k
  → prefix (xs ++ ys) σ k ≡ prefix xs (prefix ys σ) k
prefix-append [] ys σ k = refl
prefix-append (x ∷ xs) ys σ zero = refl
prefix-append (x ∷ xs) ys σ (suc k) = prefix-append xs ys σ k

advance-append : ∀ xs ys σ k
  → advance (xs ++ ys) σ k ≡ advance ys (advance xs σ) k
advance-append [] ys σ k = refl
advance-append (x ∷ xs) ys σ k = advance-append xs ys (push x σ) k

advance-reverse : ∀ xs σ k → advance xs σ k ≡ prefix (reverse xs) σ k
advance-reverse [] σ k = refl
advance-reverse (x ∷ xs) σ k =
  trans (advance-reverse xs (push x σ) k)
    (sym (trans (cong (λ ys → prefix ys σ k) (unfold-reverse x xs))
      (prefix-append (reverse xs) (x ∷ []) σ k)))

prefix-args : ∀ n xs k → prefix xs identity k ≡ argsSub-go n xs k
prefix-args n [] k = refl
prefix-args n (x ∷ xs) zero = refl
prefix-args n (x ∷ xs) (suc k) = prefix-args (suc n) xs k

-- A local declaration sees only preceding arguments, already stored in
-- de Bruijn order. This is distinct from a surface-order field list.
instantiatePrefix : List Term → Term → Term
instantiatePrefix locals ty = substS (argsSub locals) ty

instantiateFields : List Term → Term → Term
instantiateFields fields body = substS (advance fields identity) body

fields-agree : ∀ fields body
  → instantiateFields fields body ≡ substS (argsSub (reverse fields)) body
fields-agree fields body =
  cong (λ σ → substS σ body)
    (funext (λ k → trans (advance-reverse fields identity k)
      (prefix-args 0 (reverse fields) k)))

fields-vector-agree : ∀ fields bodies
  → map (instantiateFields fields) bodies ≡ substTermsS (argsSub (reverse fields)) bodies
fields-vector-agree fields [] = refl
fields-vector-agree fields (b ∷ bs) =
  cong₂ _∷_ (fields-agree fields b) (fields-vector-agree fields bs)

instantiateResult : List Term → List Term → Term → Term
instantiateResult parameters fields ty =
  substS (advance fields (advance parameters identity)) ty

result-agree : ∀ parameters fields ty
  → instantiateResult parameters fields ty
    ≡ substS (argsSub (reverse fields ++ reverse parameters)) ty
result-agree parameters fields ty =
  cong (λ σ → substS σ ty) (funext (λ k →
    trans (advance-reverse fields (advance parameters identity) k)
      (trans (cong (λ σ → prefix (reverse fields) σ k)
        (funext (advance-reverse parameters identity)))
        (trans (sym (prefix-append (reverse fields) (reverse parameters) identity k))
          (prefix-args 0 (reverse fields ++ reverse parameters) k)))))

instantiateResults : List Term → List Term → List Term → List Term
instantiateResults parameters fields = map (instantiateResult parameters fields)

result-vector-agree : ∀ parameters fields bodies
  → instantiateResults parameters fields bodies
    ≡ substTermsS (argsSub (reverse fields ++ reverse parameters)) bodies
result-vector-agree parameters fields [] = refl
result-vector-agree parameters fields (b ∷ bs) =
  cong₂ _∷_ (result-agree parameters fields b) (result-vector-agree parameters fields bs)

prefix-base : ∀ xs σ i → prefix xs σ (length xs + i) ≡ σ i
prefix-base [] σ i = refl
prefix-base (x ∷ xs) σ i = prefix-base xs σ i

advance-base : ∀ fields σ i → advance fields σ (length fields + i) ≡ σ i
advance-base fields σ i =
  trans (advance-reverse fields σ (length fields + i))
    (trans (cong (prefix (reverse fields) σ)
      (cong (_+ i) (sym (length-reverse fields))))
      (prefix-base (reverse fields) σ i))

last-at-zero : ∀ fields last σ → advance (fields ++ last ∷ []) σ zero ≡ last
last-at-zero fields last σ = advance-append fields (last ∷ []) σ zero
