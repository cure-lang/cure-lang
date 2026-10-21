------------------------------------------------------------------------
-- Expansion is a simulation of the FULL existing reduction relation.
-- Compact literal peels become ordinary constructor iota contractions.
-- No confluence, typing, termination or conversion premise is needed.
------------------------------------------------------------------------
module Proof.ExpansionSimulation where

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Reduction
open import Core.LiteralExpansion
import Core.Parallel as P

module Simulation (sig : Signature) where
  module O = P.Par (expandSig sig)

  refl-spine : ∀ xs → O._⇉*ᵗ*_ xs xs
  refl-spine [] = O.⇉ᵗ*-nil
  refl-spine (x ∷ xs) = O.⇉ᵗ*-cons O.⇉*-refl (refl-spine xs)

  ctor-path : ∀ {c xs ys} → O._⇉*ᵗ*_ xs ys
    → _⇝*_ (expandSig sig) (tm-ctor c xs) (tm-ctor c ys)
  ctor-path {xs = xs} {ys = ys} p = O.⇉→⇝*-star (O.⇉*-ctor* [] xs ys p)

  params-path : ∀ {n xs ys is} → O._⇉*ᵗ*_ xs ys
    → _⇝*_ (expandSig sig) (tm-data n xs is) (tm-data n ys is)
  params-path {xs = xs} {ys = ys} {is = is} p =
    O.⇉→⇝*-star (O.⇉*-data-params* [] xs ys is p)

  indices-path : ∀ {n ps xs ys} → O._⇉*ᵗ*_ xs ys
    → _⇝*_ (expandSig sig) (tm-data n ps xs) (tm-data n ps ys)
  indices-path {ps = ps} {xs = xs} {ys = ys} p =
    O.⇉→⇝*-star (O.⇉*-data-indices* [] xs ys ps p)

  update-path : ∀ xs (i : Fin (len xs)) {u}
    → _⇝*_ (expandSig sig) (expand (lookupAt xs i)) (expand u)
    → O._⇉*ᵗ*_ (expandTerms xs) (expandTerms (setAt xs i u))
  update-path (x ∷ xs) zero p =
    O.⇉ᵗ*-cons (O.⇝→⇉* p) (refl-spine (expandTerms xs))
  update-path (x ∷ xs) (suc i) p =
    O.⇉ᵗ*-cons O.⇉*-refl (update-path xs i p)

  mutual
    expand-step : ∀ {t u} → _⇝_ sig t u
      → _⇝*_ (expandSig sig) (expand t) (expand u)
    expand-step {t} (β {b = b} {a = a}) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-top a b)) (⇝*-step β ⇝*-refl)
    expand-step {t} (ζ {v = v} {b = b}) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-top v b)) (⇝*-step ζ ⇝*-refl)
    expand-step {t} (ι {brs = bs} {c = c} {b = b} {args = args} found len) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-args args b))
        (⇝*-step (ι (expand-lookup c bs found) (trans (expand-length args) len)) ⇝*-refl)
    expand-step {t} (ι-nat-zero {brs = bs} {b = b} found refl) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-args [] b))
        (⇝*-step (ι (expand-lookup "Z" bs found) refl) ⇝*-refl)
    expand-step {t} (ι-nat-suc {brs = bs} {b = b} {n = n} found refl) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-args (tm-nat_lit n ∷ []) b))
        (⇝*-step (ι (expand-lookup "S" bs found) refl) ⇝*-refl)
    expand-step {t} (ι-bounded-zero {brs = bs} {b = b} found refl) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-args (tm-nat_lit 0 ∷ []) b))
        (⇝*-step (ι (expand-lookup "First" bs found) refl) ⇝*-refl)
    expand-step {t} (ι-bounded-suc {brs = bs} {b = b} {k = n} found refl) =
      subst (_⇝*_ (expandSig sig) (expand t)) (sym (expand-args (tm-nat_lit n ∷ tm-bounded_lit n ∷ []) b))
        (⇝*-step (ι (expand-lookup "Next" bs found) refl) ⇝*-refl)
    expand-step (δ found) = ⇝*-step (δ (cong expandMaybe found)) ⇝*-refl
    expand-step (ξ-app₁ p) = O.⇝*-app₁ (expand-step p)
    expand-step (ξ-app₂ p) = O.⇝*-app₂ (expand-step p)
    expand-step (ξ-case p) = O.⇝*-case (expand-step p)
    expand-step (ξ-case-motive p) = O.⇝*-case-motive (expand-step p)
    expand-step (ξ-case-brs ps) = O.⇝*-case-brs (expand-branches ps)
    expand-step (ξ-effect_type p) = O.⇝*-effect_type (expand-step p)
    expand-step (ξ-effect_pure p) = O.⇝*-effect_pure (expand-step p)
    expand-step (ξ-effect_bind₁ p) = O.⇝*-effect_bind₁ (expand-step p)
    expand-step (ξ-effect_bind₂ p) = O.⇝*-effect_bind₂ (expand-step p)
    expand-step (ξ-let p) = O.⇝*-let-val (expand-step p)
    expand-step (ξ-let-ty p) = O.⇝*-let-ty (expand-step p)
    expand-step (ξ-let-body p) = O.⇝*-let-body (expand-step p)
    expand-step (ξ-ctor-at {args = args} i p) = ctor-path (update-path args i (expand-step p))
    expand-step (ξ-data-params-at {ps = ps} i p) = params-path (update-path ps i (expand-step p))
    expand-step (ξ-data-indices-at {is = is} i p) = indices-path (update-path is i (expand-step p))
    expand-step (ξ-pi-dom p) = O.⇝*-pi-dom (expand-step p)
    expand-step (ξ-pi-cod p) = O.⇝*-pi-cod (expand-step p)
    expand-step (ξ-lam-dom p) = O.⇝*-lam-dom (expand-step p)
    expand-step (ξ-lam-body p) = O.⇝*-lam-body (expand-step p)

    expand-star : ∀ {t u} → _⇝*_ sig t u
      → _⇝*_ (expandSig sig) (expand t) (expand u)
    expand-star ⇝*-refl = ⇝*-refl
    expand-star (⇝*-step p ps) = O.⇝*-trans (expand-step p) (expand-star ps)

    expand-branches : ∀ {bs cs} → _⇝*ᵇ_ sig bs cs
      → _⇝*ᵇ_ (expandSig sig) (expandBranches bs) (expandBranches cs)
    expand-branches ⇝ᵇ-nil = ⇝ᵇ-nil
    expand-branches (⇝ᵇ-cons p ps) = ⇝ᵇ-cons (expand-star p) (expand-branches ps)
