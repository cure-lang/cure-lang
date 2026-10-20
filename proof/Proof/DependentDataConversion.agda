------------------------------------------------------------------------
-- Explicit data injectivity, separate from the legacy Conversion record.
-- The reduction-model instance decomposes actual small-step paths.
------------------------------------------------------------------------
module Proof.DependentDataConversion where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Core.Syntax
open import Core.Typing using (Conversion; All2; a2[]; a2∷)
open import Core.Reduction
open import Core.LiteralExpansion using (expand; expandTerms)
open import Proof.Confluence using (ClosedBody)
import Proof.ReductionConversion as Reduction

record DataComponents (conv : Conversion) : Set where
  field
    components : ∀ {name other ps qs is js}
      → Conversion._≈_ conv (tm-data name ps is) (tm-data other qs js)
      → name ≡ other × All2 (Conversion._≈_ conv) ps qs
        × All2 (Conversion._≈_ conv) is js

module Model (sig : Signature) (closed : ClosedBody sig) where
  module R = Reduction.Model sig closed

  abstract
    paths-refl : ∀ xs → All2 (_⇝*_ R.esig) xs xs
    paths-refl [] = a2[]
    paths-refl (x ∷ xs) = a2∷ ⇝*-refl (paths-refl xs)

    paths-trans : ∀ {xs ys zs}
      → All2 (_⇝*_ R.esig) xs ys → All2 (_⇝*_ R.esig) ys zs
      → All2 (_⇝*_ R.esig) xs zs
    paths-trans a2[] a2[] = a2[]
    paths-trans (a2∷ p ps) (a2∷ q qs) =
      a2∷ (R.O.⇝*-trans p q) (paths-trans ps qs)

    path-at : ∀ {xs x′} (i : Data.Fin.Fin (len xs))
      → _⇝_ R.esig (lookupAt xs i) x′
      → All2 (_⇝*_ R.esig) xs (setAt xs i x′)
    path-at {x ∷ xs} zero p =
      a2∷ (⇝*-step p ⇝*-refl) (paths-refl xs)
    path-at {x ∷ xs} (suc i) p = a2∷ ⇝*-refl (path-at i p)

    data-path : ∀ {name ps is u}
      → _⇝*_ R.esig (tm-data name ps is) u
      → ∃ λ qs → ∃ λ js → u ≡ tm-data name qs js
        × All2 (_⇝*_ R.esig) ps qs × All2 (_⇝*_ R.esig) is js
    data-path ⇝*-refl = _ , _ , refl , paths-refl _ , paths-refl _
    data-path (⇝*-step (ξ-data-params-at i p) rest) with data-path rest
    ... | qs , js , shape , pp , ip =
      qs , js , shape , paths-trans (path-at i p) pp , ip
    data-path (⇝*-step (ξ-data-indices-at i p) rest) with data-path rest
    ... | qs , js , shape , pp , ip =
      qs , js , shape , pp , paths-trans (path-at i p) ip

    data-shape : ∀ {name other ps qs is js}
      → tm-data name ps is ≡ tm-data other qs js
      → name ≡ other × ps ≡ qs × is ≡ js
    data-shape refl = refl , refl , refl

    expanded-joins : ∀ {xs ys zs}
      → All2 (_⇝*_ R.esig) (expandTerms xs) zs
      → All2 (_⇝*_ R.esig) (expandTerms ys) zs
      → All2 (Conversion._≈_ R.conversion) xs ys
    expanded-joins {[]} {[]} a2[] a2[] = a2[]
    expanded-joins {x ∷ xs} {y ∷ ys} (a2∷ p ps) (a2∷ q qs) =
      a2∷ (_ , p , q) (expanded-joins ps qs)

    model-components : ∀ {name other ps qs is js}
      → Conversion._≈_ R.conversion (tm-data name ps is) (tm-data other qs js)
      → name ≡ other × All2 (Conversion._≈_ R.conversion) ps qs
        × All2 (Conversion._≈_ R.conversion) is js
    model-components (w , p , q) with data-path p | data-path q
    ... | ps₁ , is₁ , eq₁ , pp , ip | ps₂ , is₂ , eq₂ , pq , iq
      with data-shape (trans (sym eq₁) eq₂)
    ... | refl , refl , refl =
      refl , expanded-joins pp pq , expanded-joins ip iq

    data-components : DataComponents R.conversion
    data-components = record { components = model-components }
