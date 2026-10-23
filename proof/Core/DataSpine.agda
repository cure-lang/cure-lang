------------------------------------------------------------------------
-- Signature-aware flattened data layout MODEL. Fallback and layout are
-- not typing. Only exact finite lookup/count checks produce Alignment.
------------------------------------------------------------------------
module Core.DataSpine where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing; Maybe)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Core.Syntax using (Name)
open import Core.Signature

splitAt : ∀ {A : Set} → ℕ → List A → List A × List A
splitAt zero xs = [] , xs
splitAt (suc n) [] = [] , []
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | ps , is = x ∷ ps , is

split-preserves : ∀ {A : Set} n (xs : List A)
  → proj₁ (splitAt n xs) ++ proj₂ (splitAt n xs) ≡ xs
split-preserves zero xs = refl
split-preserves (suc n) [] = refl
split-preserves (suc n) (x ∷ xs) with splitAt n xs | split-preserves n xs
... | ps , is | equal = cong (x ∷_) equal

split-append : ∀ {A : Set} (ps is : List A) → splitAt (length ps) (ps ++ is) ≡ (ps , is)
split-append [] is = refl
split-append (p ∷ ps) is rewrite split-append ps is = refl

data Mode : Set where
  signature-free : Mode
  signature : IndEnv → Mode

split : ∀ {A : Set} → Mode → Name → List A → List A × List A
split signature-free name xs = xs , []
split (signature ind) name xs with findFamily name (IndEnv.families ind)
... | nothing = xs , []
... | just family = splitAt (length (fam-params family)) xs

mode-preserves : ∀ {A : Set} mode name (xs : List A)
  → proj₁ (split mode name xs) ++ proj₂ (split mode name xs) ≡ xs
mode-preserves signature-free name xs = ++-identityʳ xs
mode-preserves (signature ind) name xs with findFamily name (IndEnv.families ind)
... | nothing = ++-identityʳ xs
... | just family = split-preserves (length (fam-params family)) xs

canonical : ∀ {A : Set} ind name family
  → findFamily name (IndEnv.families ind) ≡ just family
  → (ps is : List A) → length ps ≡ length (fam-params family)
  → split (signature ind) name (ps ++ is) ≡ (ps , is)
canonical ind name family found ps is count rewrite found =
  trans (cong (λ n → splitAt n (ps ++ is)) (sym count)) (split-append ps is)

-- Unlike clamped splitting, Cut certifies that ALL parameter slots exist.
data Cut {A : Set} : ℕ → List A → List A → List A → Set where
  cut-zero : ∀ {xs} → Cut zero xs [] xs
  cut-cons : ∀ {n x xs ps is} → Cut n xs ps is → Cut (suc n) (x ∷ xs) (x ∷ ps) is

cut-length : ∀ {A n} {xs ps is : List A} → Cut n xs ps is → length ps ≡ n
cut-length cut-zero = refl
cut-length (cut-cons rest) = cong suc (cut-length rest)
cut-append : ∀ {A n} {xs ps is : List A} → Cut n xs ps is → ps ++ is ≡ xs
cut-append cut-zero = refl
cut-append (cut-cons {x = x} rest) = cong (x ∷_) (cut-append rest)
cut-split : ∀ {A n} {xs ps is : List A} → Cut n xs ps is → splitAt n xs ≡ (ps , is)
cut-split cut-zero = refl
cut-split (cut-cons rest) rewrite cut-split rest = refl

prefix : ∀ {A : Set} (n : ℕ) (xs : List A) → Maybe (Σ (List A) λ ps → Σ (List A) λ is → Cut n xs ps is)
prefix zero xs = just ([] , xs , cut-zero)
prefix (suc n) [] = nothing
prefix (suc n) (x ∷ xs) with prefix n xs
... | nothing = nothing
... | just (ps , is , cut) = just (x ∷ ps , is , cut-cons cut)

record Alignment {A : Set} (ind : IndEnv) (name : Name) (xs : List A) : Set where
  constructor aligned
  field
    family : Family
    found : findFamily name (IndEnv.families ind) ≡ just family
    parameters indices : List A
    parameter-prefix : Cut (length (fam-params family)) xs parameters indices
    index-count : length indices ≡ length (fam-indices family)
  parameter-count : length parameters ≡ length (fam-params family)
  parameter-count = cut-length parameter-prefix
  flattened : parameters ++ indices ≡ xs
  flattened = cut-append parameter-prefix
  selected : split (signature ind) name xs ≡ (parameters , indices)
  selected rewrite found = cut-split parameter-prefix

data Failure : Set where
  unknown-family missing-parameters wrong-index-arity : Failure
data Result (A : Set) : Set where
  accepted : A → Result A
  rejected : Failure → Result A
check : ∀ {A : Set} (ind : IndEnv) (name : Name) (xs : List A) → Result (Alignment ind name xs)
check ind name xs with findFamily name (IndEnv.families ind) in found
... | nothing = rejected unknown-family
... | just family with prefix (length (fam-params family)) xs
... | nothing = rejected missing-parameters
... | just (ps , is , cut) with Nat._≟_ (length is) (length (fam-indices family))
... | no _ = rejected wrong-index-arity
... | yes count = accepted (aligned family found ps is cut count)
