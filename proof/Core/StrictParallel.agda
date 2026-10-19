------------------------------------------------------------------------
-- Genuine ONE-STEP parallel reduction. Every recursive premise is a
-- single parallel step, including branch bodies; there are NO Star
-- premises. The older Core.Parallel remains a checked simulation layer.
-- Small-step branch congruence may contain arbitrarily long finite paths,
-- so the inclusion here is small-step ⊆ STRICT-PARALLEL STAR, not one step.
------------------------------------------------------------------------
module Core.StrictParallel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax
open import Core.Reduction
open import Core.Relation
import Core.Parallel as Old

data Atom : Term → Set where
  a-type : ∀ {l} → Atom (tm-type l)
  a-var : ∀ {k} → Atom (tm-var k)
  a-global : ∀ {n} → Atom (tm-global n)
  a-int-type : Atom tm-int_type
  a-int : ∀ {k} → Atom (tm-int_lit k)
  a-nat : ∀ {k} → Atom (tm-nat_lit k)
  a-bounded : ∀ {k} → Atom (tm-bounded_lit k)
  a-float-type : Atom tm-float_type
  a-float : Atom tm-float_lit
  a-binary : Atom tm-binary_type
  a-atom-type : Atom tm-atom_type
  a-atom : ∀ {n} → Atom (tm-atom_lit n)
  a-hole : ∀ {n} → Atom (tm-hole n)
  a-absurd : Atom tm-absurd

module Parallel (sig : Signature) where
  module O = Old.Par sig
  infix 4 _⇛_ _⇛ᵗ_ _⇛ᵇ_
  mutual
    data _⇛_ : Term → Term → Set where
      s-atom : ∀ {t} → Atom t → t ⇛ t
      s-pi : ∀ {g d d′ c c′} → d ⇛ d′ → c ⇛ c′ → tm-pi g d c ⇛ tm-pi g d′ c′
      s-lam : ∀ {g d d′ b b′} → d ⇛ d′ → b ⇛ b′ → tm-lam g d b ⇛ tm-lam g d′ b′
      s-let : ∀ {g ty ty′ v v′ b b′} → ty ⇛ ty′ → v ⇛ v′ → b ⇛ b′
        → tm-let g ty v b ⇛ tm-let g ty′ v′ b′
      s-app : ∀ {f f′ a a′} → f ⇛ f′ → a ⇛ a′ → tm-app f a ⇛ tm-app f′ a′
      s-data : ∀ {n ps ps′ is is′} → ps ⇛ᵗ ps′ → is ⇛ᵗ is′ → tm-data n ps is ⇛ tm-data n ps′ is′
      s-ctor : ∀ {n args args′} → args ⇛ᵗ args′ → tm-ctor n args ⇛ tm-ctor n args′
      s-case : ∀ {s s′ m m′ bs bs′} → s ⇛ s′ → m ⇛ m′ → bs ⇛ᵇ bs′
        → tm-case s m bs ⇛ tm-case s′ m′ bs′
      s-effect-type : ∀ {a a′} → a ⇛ a′ → tm-effect_type a ⇛ tm-effect_type a′
      s-effect-pure : ∀ {a a′} → a ⇛ a′ → tm-effect_pure a ⇛ tm-effect_pure a′
      s-effect-bind : ∀ {e e′ k k′} → e ⇛ e′ → k ⇛ k′ → tm-effect_bind e k ⇛ tm-effect_bind e′ k′
      s-beta : ∀ {g d d′ b b′ a a′} → d ⇛ d′ → b ⇛ b′ → a ⇛ a′
        → tm-app (tm-lam g d b) a ⇛ substTopT a′ b′
      s-zeta : ∀ {g ty ty′ v v′ b b′} → ty ⇛ ty′ → v ⇛ v′ → b ⇛ b′
        → tm-let g ty v b ⇛ substTopT v′ b′
      s-iota : ∀ {m m′ bs bs′ c ar b args args′}
        → findBranch c bs′ ≡ just (c , ar , b) → length args ≡ ar
        → m ⇛ m′ → bs ⇛ᵇ bs′ → args ⇛ᵗ args′
        → tm-case (tm-ctor c args) m bs ⇛ substArgs args′ b
      s-nat-zero : ∀ {m m′ bs bs′ b}
        → findBranch "Z" bs′ ≡ just ("Z" , 0 , b) → m ⇛ m′ → bs ⇛ᵇ bs′
        → tm-case (tm-nat_lit 0) m bs ⇛ substArgs [] b
      s-nat-suc : ∀ {m m′ bs bs′ b n}
        → findBranch "S" bs′ ≡ just ("S" , 1 , b) → m ⇛ m′ → bs ⇛ᵇ bs′
        → tm-case (tm-nat_lit (suc n)) m bs ⇛ substArgs (tm-nat_lit n ∷ []) b
      s-bounded-zero : ∀ {m m′ bs bs′ b}
        → findBranch "First" bs′ ≡ just ("First" , 1 , b) → m ⇛ m′ → bs ⇛ᵇ bs′
        → tm-case (tm-bounded_lit 0) m bs ⇛ substArgs (tm-nat_lit 0 ∷ []) b
      s-bounded-suc : ∀ {m m′ bs bs′ b n}
        → findBranch "Next" bs′ ≡ just ("Next" , 2 , b) → m ⇛ m′ → bs ⇛ᵇ bs′
        → tm-case (tm-bounded_lit (suc n)) m bs ⇛ substArgs (tm-nat_lit n ∷ tm-bounded_lit n ∷ []) b
      s-delta : ∀ {f b} → Signature.body sig f ≡ just b → tm-global f ⇛ b

    data _⇛ᵗ_ : List Term → List Term → Set where
      st-nil : [] ⇛ᵗ []
      st-cons : ∀ {x y xs ys} → x ⇛ y → xs ⇛ᵗ ys → (x ∷ xs) ⇛ᵗ (y ∷ ys)

    data _⇛ᵇ_ : List Branch → List Branch → Set where
      sb-nil : [] ⇛ᵇ []
      sb-cons : ∀ {cn ar b b′ bs bs′} → b ⇛ b′ → bs ⇛ᵇ bs′
        → ((cn , ar , b) ∷ bs) ⇛ᵇ ((cn , ar , b′) ∷ bs′)

  mutual
    reflexive : ∀ t → t ⇛ t
    reflexive (tm-type l) = s-atom a-type
    reflexive (tm-var k) = s-atom a-var
    reflexive (tm-pi g d c) = s-pi (reflexive d) (reflexive c)
    reflexive (tm-lam g d b) = s-lam (reflexive d) (reflexive b)
    reflexive (tm-let g ty v b) = s-let (reflexive ty) (reflexive v) (reflexive b)
    reflexive (tm-app f a) = s-app (reflexive f) (reflexive a)
    reflexive (tm-data n ps is) = s-data (terms-refl ps) (terms-refl is)
    reflexive (tm-ctor n args) = s-ctor (terms-refl args)
    reflexive (tm-case s m bs) = s-case (reflexive s) (reflexive m) (branches-refl bs)
    reflexive (tm-global n) = s-atom a-global
    reflexive tm-int_type = s-atom a-int-type
    reflexive (tm-int_lit k) = s-atom a-int
    reflexive (tm-nat_lit k) = s-atom a-nat
    reflexive (tm-bounded_lit k) = s-atom a-bounded
    reflexive tm-float_type = s-atom a-float-type
    reflexive tm-float_lit = s-atom a-float
    reflexive tm-binary_type = s-atom a-binary
    reflexive tm-atom_type = s-atom a-atom-type
    reflexive (tm-atom_lit n) = s-atom a-atom
    reflexive (tm-effect_type a) = s-effect-type (reflexive a)
    reflexive (tm-effect_pure a) = s-effect-pure (reflexive a)
    reflexive (tm-effect_bind e k) = s-effect-bind (reflexive e) (reflexive k)
    reflexive (tm-hole n) = s-atom a-hole
    reflexive tm-absurd = s-atom a-absurd

    terms-refl : ∀ xs → xs ⇛ᵗ xs
    terms-refl [] = st-nil
    terms-refl (x ∷ xs) = st-cons (reflexive x) (terms-refl xs)

    branches-refl : ∀ bs → bs ⇛ᵇ bs
    branches-refl [] = sb-nil
    branches-refl ((cn , ar , b) ∷ bs) = sb-cons (reflexive b) (branches-refl bs)

  terms-length : ∀ {xs ys} → xs ⇛ᵗ ys → length ys ≡ length xs
  terms-length st-nil = refl
  terms-length (st-cons p ps) = cong suc (terms-length ps)

  mutual
    -- Embed in the already checked simulation, NOT the old confluence
    -- theorem. No function from Proof.Confluence is used here.
    embed : ∀ {t u} → t ⇛ u → O._⇉_ t u
    embed (s-atom a-type) = O.p-type
    embed (s-atom a-var) = O.p-var
    embed (s-atom a-global) = O.p-global
    embed (s-atom a-int-type) = O.p-int_type
    embed (s-atom a-int) = O.p-int_lit
    embed (s-atom a-nat) = O.p-nat_lit
    embed (s-atom a-bounded) = O.p-bounded_lit
    embed (s-atom a-float-type) = O.p-float_type
    embed (s-atom a-float) = O.p-float_lit
    embed (s-atom a-binary) = O.p-binary_type
    embed (s-atom a-atom-type) = O.p-atom_type
    embed (s-atom a-atom) = O.p-atom_lit
    embed (s-atom a-hole) = O.p-hole
    embed (s-atom a-absurd) = O.p-absurd
    embed (s-pi p q) = O.p-pi (embed p) (embed q)
    embed (s-lam p q) = O.p-lam (embed p) (embed q)
    embed (s-let p q r) = O.p-let (embed p) (embed q) (embed r)
    embed (s-app p q) = O.p-app (embed p) (embed q)
    embed (s-data p q) = O.p-data (embed-terms p) (embed-terms q)
    embed (s-ctor p) = O.p-ctor (embed-terms p)
    embed (s-case p q r) = O.p-case (embed p) (embed q) (embed-branches r)
    embed (s-effect-type p) = O.p-effect_type (embed p)
    embed (s-effect-pure p) = O.p-effect_pure (embed p)
    embed (s-effect-bind p q) = O.p-effect_bind (embed p) (embed q)
    embed (s-beta p q r) = O.p-β (embed p) (O.⇉*-step (embed q) O.⇉*-refl) (embed r)
    embed (s-zeta p q r) = O.p-ζ (embed p) (embed q) (O.⇉*-step (embed r) O.⇉*-refl)
    embed (s-iota found len m bs args) =
      O.p-ι found len (embed m) (embed-branches bs) O.⇉*-refl (embed-terms args)
    embed (s-nat-zero found m bs) = O.p-ι-nat-zero found refl (embed m) (embed-branches bs) O.⇉*-refl
    embed (s-nat-suc found m bs) = O.p-ι-nat-suc found refl (embed m) (embed-branches bs) O.⇉*-refl
    embed (s-bounded-zero found m bs) = O.p-ι-bounded-zero found refl (embed m) (embed-branches bs) O.⇉*-refl
    embed (s-bounded-suc found m bs) = O.p-ι-bounded-suc found refl (embed m) (embed-branches bs) O.⇉*-refl
    embed (s-delta found) = O.p-δ found

    embed-terms : ∀ {xs ys} → xs ⇛ᵗ ys → O._⇉*ᵗ_ xs ys
    embed-terms st-nil = O.⇉*-nil
    embed-terms (st-cons p ps) = O.⇉*-cons (embed p) (embed-terms ps)

    embed-branches : ∀ {bs cs} → bs ⇛ᵇ cs → O._⇉*ᵇ_ bs cs
    embed-branches sb-nil = O.⇉ᵇ-nil
    embed-branches (sb-cons p ps) =
      O.⇉ᵇ-cons (O.⇉*-step (embed p) O.⇉*-refl) (embed-branches ps)

  to-small : ∀ {t u} → Star _⇛_ t u → _⇝*_ sig t u
  to-small done = ⇝*-refl
  to-small (step p ps) = O.⇝*-trans (O.⇉→⇝* (embed p)) (to-small ps)

  at : (xs : List Term) (i : Fin (len xs)) {u : Term}
    → lookupAt xs i ⇛ u → xs ⇛ᵗ setAt xs i u
  at (x ∷ xs) zero p = st-cons p (terms-refl xs)
  at (x ∷ xs) (suc i) p = st-cons (reflexive x) (at xs i p)

  at-star : (xs : List Term) (i : Fin (len xs)) {u : Term}
    → Star _⇛_ (lookupAt xs i) u → Star _⇛ᵗ_ xs (setAt xs i u)
  at-star (x ∷ xs) zero ps =
    map-star (λ t → t ∷ xs) (λ s → st-cons s (terms-refl xs)) ps
  at-star (x ∷ xs) (suc i) ps =
    map-star (x ∷_) (λ s → st-cons (reflexive x) s) (at-star xs i ps)

  mutual
    from-small : ∀ {t u} → _⇝_ sig t u → Star _⇛_ t u
    from-small β = step (s-beta (reflexive _) (reflexive _) (reflexive _)) done
    from-small ζ = step (s-zeta (reflexive _) (reflexive _) (reflexive _)) done
    from-small (ι found len) = step (s-iota found len (reflexive _) (branches-refl _) (terms-refl _)) done
    from-small (ι-nat-zero found refl) = step (s-nat-zero found (reflexive _) (branches-refl _)) done
    from-small (ι-nat-suc found refl) = step (s-nat-suc found (reflexive _) (branches-refl _)) done
    from-small (ι-bounded-zero found refl) = step (s-bounded-zero found (reflexive _) (branches-refl _)) done
    from-small (ι-bounded-suc found refl) = step (s-bounded-suc found (reflexive _) (branches-refl _)) done
    from-small (δ found) = step (s-delta found) done
    from-small (ξ-app₁ p) = map-star (λ f → tm-app f _) (λ s → s-app s (reflexive _)) (from-small p)
    from-small (ξ-app₂ p) = map-star (tm-app _) (λ s → s-app (reflexive _) s) (from-small p)
    from-small (ξ-case p) = map-star (λ s → tm-case s _ _) (λ s → s-case s (reflexive _) (branches-refl _)) (from-small p)
    from-small (ξ-case-motive p) = map-star (λ m → tm-case _ m _) (λ s → s-case (reflexive _) s (branches-refl _)) (from-small p)
    from-small (ξ-case-brs ps) =
      map-star (tm-case _ _) (λ s → s-case (reflexive _) (reflexive _) s) (from-small-branches ps)
    from-small (ξ-effect_type p) = map-star tm-effect_type s-effect-type (from-small p)
    from-small (ξ-effect_pure p) = map-star tm-effect_pure s-effect-pure (from-small p)
    from-small (ξ-effect_bind₁ p) = map-star (λ e → tm-effect_bind e _) (λ s → s-effect-bind s (reflexive _)) (from-small p)
    from-small (ξ-effect_bind₂ p) = map-star (tm-effect_bind _) (λ s → s-effect-bind (reflexive _) s) (from-small p)
    from-small (ξ-let p) = map-star (λ v → tm-let _ _ v _) (λ s → s-let (reflexive _) s (reflexive _)) (from-small p)
    from-small (ξ-let-ty p) = map-star (λ ty → tm-let _ ty _ _) (λ s → s-let s (reflexive _) (reflexive _)) (from-small p)
    from-small (ξ-let-body p) = map-star (tm-let _ _ _) (λ s → s-let (reflexive _) (reflexive _) s) (from-small p)
    from-small (ξ-ctor-at {n = c} {args = args} i p) =
      map-star (tm-ctor c) s-ctor (at-star args i (from-small p))
    from-small (ξ-data-params-at {n = n} {is = is} {ps = ps} i p) =
      map-star (λ ts → tm-data n ts is) (λ s → s-data s (terms-refl is)) (at-star ps i (from-small p))
    from-small (ξ-data-indices-at {n = n} {ps = ps} {is = is} i p) =
      map-star (tm-data n ps) (λ s → s-data (terms-refl ps) s) (at-star is i (from-small p))
    from-small (ξ-pi-dom p) = map-star (λ d → tm-pi _ d _) (λ s → s-pi s (reflexive _)) (from-small p)
    from-small (ξ-pi-cod p) = map-star (tm-pi _ _) (λ s → s-pi (reflexive _) s) (from-small p)
    from-small (ξ-lam-dom p) = map-star (λ d → tm-lam _ d _) (λ s → s-lam s (reflexive _)) (from-small p)
    from-small (ξ-lam-body p) = map-star (tm-lam _ _) (λ s → s-lam (reflexive _) s) (from-small p)

    from-small-star : ∀ {t u} → _⇝*_ sig t u → Star _⇛_ t u
    from-small-star ⇝*-refl = done
    from-small-star (⇝*-step p ps) = append (from-small p) (from-small-star ps)

    from-small-branches : ∀ {bs cs} → _⇝*ᵇ_ sig bs cs → Star _⇛ᵇ_ bs cs
    from-small-branches ⇝ᵇ-nil = done
    from-small-branches (⇝ᵇ-cons {cn = cn} {ar = ar} {b′ = b′} {bs = bs} p ps) =
      append (map-star (λ b → (cn , ar , b) ∷ bs)
                       (λ s → sb-cons s (branches-refl bs)) (from-small-star p))
             (map-star (λ tail → (cn , ar , b′) ∷ tail)
                       (λ s → sb-cons (reflexive b′) s) (from-small-branches ps))
