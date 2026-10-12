------------------------------------------------------------------------
-- Parallel reduction ⇉ (the Tait–Martin-Löf method).
--
-- WHY PARALLEL REDUCTION. The reduction relation `_⇝_` (Core/Reduction.agda)
-- is NOT deterministic: `(λx. b) a` both β-reduces (the `β` rule) AND reduces
-- under the λ (the `ξ-lam-body` congruence). This non-determinism is exactly
-- what blocks a direct proof of CONFLUENCE of `_⇝_`, and it is why the
-- classical soundness theorem's second input (`never-reached→no-value`,
-- Proof/Soundness.agda) is carried as a postulate.
--
-- The Tait–Martin-Löf method resolves it: define a PARALLEL reduction `_⇉_`
-- that contracts ALL redexes of a term in one step, prove the DIAMOND property
-- for `_⇉_`, and read confluence of `_⇝_` off the two inclusions
--
--     _⇝_  ⊆  _⇉_        (every single step is a parallel step)
--     _⇉_  ⊆  _⇝*_       (every parallel step is a sequence of single steps)
--
-- This module defines `_⇉_` and the two inclusions. The diamond property
-- lives in Proof/Confluence.agda.
--
-- `_⇝_`'s spine congruences are ELEMENT-INDEXED (`ξ-ctor-at` / `ξ-data-*-at`,
-- a `Fin` into the spine), which is what makes `⇉ ⊆ ⇝*` provable: a parallel
-- spine reduction is simulated by reducing one element at a time.
------------------------------------------------------------------------
module Core.Parallel where

open import Data.Bool using (Bool; true; false)
open import Data.String.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; length; map; find; reverse)
open import Data.List using () renaming (lookup to listLookup)
open import Data.Fin using (Fin; zero; suc; toℕ; cast)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax
open import Core.Signature using (just-inj)
open import Core.Reduction

------------------------------------------------------------------------
-- Parallel reduction.
------------------------------------------------------------------------


module Par (sig : Signature) where

  infix 4 _⇉_

  mutual

    data _⇉_ : Term → Term → Set where

      -- Atomic / neutral forms reduce to themselves.
      p-type   : ∀ {l} → tm-type l ⇉ tm-type l
      p-var    : ∀ {k} → tm-var k ⇉ tm-var k
      p-global : ∀ {n} → tm-global n ⇉ tm-global n
      p-int_type    : tm-int_type ⇉ tm-int_type
      p-int_lit     : ∀ {k} → tm-int_lit k ⇉ tm-int_lit k
      p-nat_lit     : ∀ {k} → tm-nat_lit k ⇉ tm-nat_lit k
      p-bounded_lit : ∀ {k} → tm-bounded_lit k ⇉ tm-bounded_lit k
      p-float_type  : tm-float_type ⇉ tm-float_type
      p-float_lit   : tm-float_lit ⇉ tm-float_lit
      p-binary_type : tm-binary_type ⇉ tm-binary_type
      p-atom_type   : tm-atom_type ⇉ tm-atom_type
      p-atom_lit    : ∀ {n} → tm-atom_lit n ⇉ tm-atom_lit n
      p-hole   : ∀ {n} → tm-hole n ⇉ tm-hole n
      p-absurd : tm-absurd ⇉ tm-absurd

      -- Structural congruences: contract every subterm at once.
      p-pi : ∀ {g d d′ c c′} → d ⇉ d′ → c ⇉ c′ → tm-pi g d c ⇉ tm-pi g d′ c′
      p-lam : ∀ {g d d′ b b′} → d ⇉ d′ → b ⇉ b′ → tm-lam g d b ⇉ tm-lam g d′ b′
      p-let : ∀ {g ty ty′ v v′ b b′} → ty ⇉ ty′ → v ⇉ v′ → b ⇉ b′
            → tm-let g ty v b ⇉ tm-let g ty′ v′ b′
      p-app : ∀ {f f′ a a′} → f ⇉ f′ → a ⇉ a′ → tm-app f a ⇉ tm-app f′ a′
      p-data : ∀ {n ps ps′ is is′} → ps ⇉*ᵗ ps′ → is ⇉*ᵗ is′
             → tm-data n ps is ⇉ tm-data n ps′ is′
      p-ctor : ∀ {n args args′} → args ⇉*ᵗ args′ → tm-ctor n args ⇉ tm-ctor n args′
      -- Head/tail rules for the spine (used to simulate a parallel spine
      -- reduction by `_⇝_` one element at a time, without index arithmetic).
      p-ctor-head : ∀ {n x x′ xs} → x ⇉ x′ → tm-ctor n (x ∷ xs) ⇉ tm-ctor n (x′ ∷ xs)
      p-ctor-tail : ∀ {n x xs xs′} → tm-ctor n xs ⇉ tm-ctor n xs′
                  → tm-ctor n (x ∷ xs) ⇉ tm-ctor n (x ∷ xs′)
      p-case : ∀ {s s′ m m′ brs brs′} → s ⇉ s′ → m ⇉ m′ → brs ⇉*ᵇ brs′
             → tm-case s m brs ⇉ tm-case s′ m′ brs′
      p-effect_type : ∀ {t t′} → t ⇉ t′ → tm-effect_type t ⇉ tm-effect_type t′
      p-effect_pure : ∀ {t t′} → t ⇉ t′ → tm-effect_pure t ⇉ tm-effect_pure t′
      p-effect_bind : ∀ {e e′ k k′} → e ⇉ e′ → k ⇉ k′
                    → tm-effect_bind e k ⇉ tm-effect_bind e′ k′

      -- β: contract the redex AND its subterms at once. The argument `a` is
      -- a VALUE (the same side condition as `_⇝_`'s β rule), and its parallel
      -- reduct `a′` is ALSO a value.
      p-β : ∀ {g d d′ b b′ a a′}
          → Value a → Value a′ → d ⇉ d′ → b ⇉ b′ → a ⇉ a′
          → tm-app (tm-lam g d b) a ⇉ substTopT a′ b′

      -- ζ: let x = v in b ⇉ b′[x := v′], with `v` and `v′` values.
      p-ζ : ∀ {g ty ty′ v v′ b b′}
          → Value v → Value v′ → ty ⇉ ty′ → v ⇉ v′ → b ⇉ b′
          → tm-let g ty v b ⇉ substTopT v′ b′

      -- ι: case (ctor c args) of … ⇉ b[args′] (the branch body `b` is taken
      -- from `findBranch`, matching `_⇝_`'s ι rule).
      p-ι : ∀ {m m′ brs c ar b args args′}
          → findBranch c brs ≡ just (c , ar , b)
          → length args ≡ ar
          → m ⇉ m′ → args ⇉*ᵗ args′
          → tm-case (tm-ctor c args) m brs ⇉ substArgs args′ b

      -- ι-nat / ι-bounded: the compact-literal peels.
      p-ι-nat-zero : ∀ {m m′ brs ar b}
        → findBranch "Z" brs ≡ just ("Z" , ar , b)
        → m ⇉ m′
        → tm-case (tm-nat_lit 0) m brs ⇉ substArgs [] b

      p-ι-nat-suc : ∀ {m m′ brs ar b n}
        → findBranch "S" brs ≡ just ("S" , ar , b)
        → m ⇉ m′
        → tm-case (tm-nat_lit (suc n)) m brs ⇉ substArgs (tm-nat_lit n ∷ []) b

      p-ι-bounded-zero : ∀ {m m′ brs ar b}
        → findBranch "First" brs ≡ just ("First" , ar , b)
        → m ⇉ m′
        → tm-case (tm-bounded_lit 0) m brs ⇉ substArgs (tm-nat_lit 0 ∷ []) b

      p-ι-bounded-suc : ∀ {m m′ brs ar b k}
        → findBranch "Next" brs ≡ just ("Next" , ar , b)
        → m ⇉ m′
        → tm-case (tm-bounded_lit (suc k)) m brs
          ⇉ substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b

      -- δ: unfold a certified global to its body.
      p-δ : ∀ {f body′} → Signature.body sig f ≡ just body′ → tm-global f ⇉ body′

    -- Multi-step parallel reduction.
    data _⇉*_ : Term → Term → Set where
      ⇉*-refl : ∀ {t} → t ⇉* t
      ⇉*-step : ∀ {t u v} → t ⇉ u → u ⇉* v → t ⇉* v

    data _⇉*ᵗ_ : List Term → List Term → Set where
      ⇉*-nil  : [] ⇉*ᵗ []
      ⇉*-cons : ∀ {x x′ xs xs′} → x ⇉ x′ → xs ⇉*ᵗ xs′ → (x ∷ xs) ⇉*ᵗ (x′ ∷ xs′)

    -- List-wise MULTI-step branch reduction (each body reduces by `_⇉*_`).
    data _⇉*ᵇ_ : List Branch → List Branch → Set where
      ⇉ᵇ-nil  : [] ⇉*ᵇ []
      ⇉ᵇ-cons : ∀ {cn ar b b′ bs bs′} → b ⇉* b′ → bs ⇉*ᵇ bs′
              → ((cn , ar , b) ∷ bs) ⇉*ᵇ ((cn , ar , b′) ∷ bs′)

  ------------------------------------------------------------------------
  -- Reflexivity of `_⇉_`.
  ------------------------------------------------------------------------

  mutual
    ⇉-refl : ∀ (t : Term) → _⇉_ t t
    ⇉-refl (tm-type l) = p-type
    ⇉-refl (tm-var k) = p-var
    ⇉-refl (tm-pi g d c) = p-pi (⇉-refl d) (⇉-refl c)
    ⇉-refl (tm-lam g d b) = p-lam (⇉-refl d) (⇉-refl b)
    ⇉-refl (tm-let g ty v b) = p-let (⇉-refl ty) (⇉-refl v) (⇉-refl b)
    ⇉-refl (tm-app f a) = p-app (⇉-refl f) (⇉-refl a)
    ⇉-refl (tm-data n ps is) = p-data (⇉-refl-terms ps) (⇉-refl-terms is)
    ⇉-refl (tm-ctor n args) = p-ctor (⇉-refl-terms args)
    ⇉-refl (tm-case s m brs) = p-case (⇉-refl s) (⇉-refl m) (⇉-refl-brs brs)
    ⇉-refl (tm-global n) = p-global
    ⇉-refl (tm-int_type) = p-int_type
    ⇉-refl (tm-int_lit k) = p-int_lit
    ⇉-refl (tm-nat_lit k) = p-nat_lit
    ⇉-refl (tm-bounded_lit k) = p-bounded_lit
    ⇉-refl (tm-float_type) = p-float_type
    ⇉-refl (tm-float_lit) = p-float_lit
    ⇉-refl (tm-binary_type) = p-binary_type
    ⇉-refl (tm-atom_type) = p-atom_type
    ⇉-refl (tm-atom_lit n) = p-atom_lit
    ⇉-refl (tm-effect_type t) = p-effect_type (⇉-refl t)
    ⇉-refl (tm-effect_pure t) = p-effect_pure (⇉-refl t)
    ⇉-refl (tm-effect_bind e k) = p-effect_bind (⇉-refl e) (⇉-refl k)
    ⇉-refl (tm-hole n) = p-hole
    ⇉-refl (tm-absurd) = p-absurd

    ⇉-refl-terms : ∀ (ts : List Term) → _⇉*ᵗ_ ts ts
    ⇉-refl-terms [] = ⇉*-nil
    ⇉-refl-terms (x ∷ xs) = ⇉*-cons (⇉-refl x) (⇉-refl-terms xs)

    ⇉-refl-brs : ∀ (bs : List Branch) → _⇉*ᵇ_ bs bs
    ⇉-refl-brs [] = ⇉ᵇ-nil
    ⇉-refl-brs ((cn , ar , b) ∷ bs) = ⇉ᵇ-cons (⇉*-refl) (⇉-refl-brs bs)

  ------------------------------------------------------------------------
  -- `_⇝_ ⊆ _⇉_`.
  ------------------------------------------------------------------------

  mutual
    ⇝→⇉ : ∀ {t t′} → _⇝_ sig t t′ → _⇉_ t t′
    ⇝→⇉ (β {g} {d} {b} {a} va) =
      p-β va va (⇉-refl d) (⇉-refl b) (⇉-refl a)
    ⇝→⇉ (ζ {g} {ty} {v} {b} vv) =
      p-ζ vv vv (⇉-refl ty) (⇉-refl v) (⇉-refl b)
    ⇝→⇉ (ι {m} {brs} {c} {ar} {b} {args} found len) =
      p-ι found len (⇉-refl m) (⇉-refl-terms args)
    ⇝→⇉ (ι-nat-zero {m} {brs} {ar} {b} found) =
      p-ι-nat-zero found (⇉-refl m)
    ⇝→⇉ (ι-nat-suc {m} {brs} {ar} {b} {n} found) =
      p-ι-nat-suc found (⇉-refl m)
    ⇝→⇉ (ι-bounded-zero {m} {brs} {ar} {b} found) =
      p-ι-bounded-zero found (⇉-refl m)
    ⇝→⇉ (ι-bounded-suc {m} {brs} {ar} {b} {k} found) =
      p-ι-bounded-suc found (⇉-refl m)
    ⇝→⇉ (δ eq) = p-δ eq
    ⇝→⇉ (ξ-app₁ step) = p-app (⇝→⇉ step) (⇉-refl _)
    ⇝→⇉ (ξ-app₂ step) = p-app (⇉-refl _) (⇝→⇉ step)
    ⇝→⇉ (ξ-case step) = p-case (⇝→⇉ step) (⇉-refl _) (⇉-refl-brs _)
    ⇝→⇉ (ξ-case-motive step) = p-case (⇉-refl _) (⇝→⇉ step) (⇉-refl-brs _)
    ⇝→⇉ (ξ-case-brs steps) = p-case (⇉-refl _) (⇉-refl _) (⇝→⇉-brs steps)
    ⇝→⇉ (ξ-effect_type step) = p-effect_type (⇝→⇉ step)
    ⇝→⇉ (ξ-effect_pure step) = p-effect_pure (⇝→⇉ step)
    ⇝→⇉ (ξ-effect_bind₁ step) = p-effect_bind (⇝→⇉ step) (⇉-refl _)
    ⇝→⇉ (ξ-effect_bind₂ step) = p-effect_bind (⇉-refl _) (⇝→⇉ step)
    ⇝→⇉ (ξ-let step) = p-let (⇉-refl _) (⇝→⇉ step) (⇉-refl _)
    ⇝→⇉ (ξ-let-ty step) = p-let (⇝→⇉ step) (⇉-refl _) (⇉-refl _)
    ⇝→⇉ (ξ-let-body step) = p-let (⇉-refl _) (⇉-refl _) (⇝→⇉ step)
    ⇝→⇉ (ξ-ctor-at {args = args} i step) = p-ctor (⇉-at args i (⇝→⇉ step))
    ⇝→⇉ (ξ-data-params-at {ps = ps} i step) = p-data (⇉-at ps i (⇝→⇉ step)) (⇉-refl-terms _)
    ⇝→⇉ (ξ-data-indices-at {is = is} i step) = p-data (⇉-refl-terms _) (⇉-at is i (⇝→⇉ step))
    ⇝→⇉ (ξ-pi-dom step) = p-pi (⇝→⇉ step) (⇉-refl _)
    ⇝→⇉ (ξ-pi-cod step) = p-pi (⇉-refl _) (⇝→⇉ step)
    ⇝→⇉ (ξ-lam-dom step) = p-lam (⇝→⇉ step) (⇉-refl _)
    ⇝→⇉ (ξ-lam-body step) = p-lam (⇉-refl _) (⇝→⇉ step)

    ⇝→⇉-terms : ∀ {ts ts′} → _⇝*ᵗ_ sig ts ts′ → _⇉*ᵗ_ ts ts′
    ⇝→⇉-terms ⇝*-nil = ⇉*-nil
    ⇝→⇉-terms (⇝*-cons step steps) = ⇉*-cons (⇝→⇉ step) (⇝→⇉-terms steps)

    ⇝→⇉-brs : ∀ {bs bs′} → _⇝*ᵇ_ sig bs bs′ → _⇉*ᵇ_ bs bs′
    ⇝→⇉-brs ⇝ᵇ-nil = ⇉ᵇ-nil
    ⇝→⇉-brs (⇝ᵇ-cons steps steps′) = ⇉ᵇ-cons (⇝→⇉* steps) (⇝→⇉-brs steps′)

    ⇝→⇉* : ∀ {t t′} → _⇝*_ sig t t′ → _⇉*_ t t′
    ⇝→⇉* ⇝*-refl = ⇉*-refl
    ⇝→⇉* (⇝*-step s ss) = ⇉*-step (⇝→⇉ s) (⇝→⇉* ss)

    -- Update the element at `i` by a parallel step, leaving the rest by
    -- reflexivity.
    ⇉-at : ∀ (xs : List Term) (i : Fin (len xs)) {x′}
         → _⇉_ (lookupAt xs i) x′ → _⇉*ᵗ_ xs (setAt xs i x′)
    ⇉-at (y ∷ ys) zero sx = ⇉*-cons sx (⇉-refl-terms ys)
    ⇉-at (y ∷ ys) (suc i) sx = ⇉*-cons (⇉-refl y) (⇉-at ys i sx)

  ------------------------------------------------------------------------
  -- `_⇉_ ⊆ _⇝*_`.
  ------------------------------------------------------------------------

  -- Transitivity of the multi-step reduction.
  ⇝*-trans : ∀ {t u v} → _⇝*_ sig t u → _⇝*_ sig u v → _⇝*_ sig t v
  ⇝*-trans ⇝*-refl q = q
  ⇝*-trans (⇝*-step s ss) q = ⇝*-step s (⇝*-trans ss q)

  -- Parallel reduction preserves the length of a term spine.
  ⇉-terms-length : ∀ {xs xs′} → _⇉*ᵗ_ xs xs′ → length xs′ ≡ length xs
  ⇉-terms-length ⇉*-nil = refl
  ⇉-terms-length (⇉*-cons _ ss) = cong suc (⇉-terms-length ss)

  -- Multi-step congruence lifters.
  ⇝*-pi-dom : ∀ {g d d′ c} → _⇝*_ sig d d′ → _⇝*_ sig (tm-pi g d c) (tm-pi g d′ c)
  ⇝*-pi-dom ⇝*-refl = ⇝*-refl
  ⇝*-pi-dom (⇝*-step s ss) = ⇝*-step (ξ-pi-dom s) (⇝*-pi-dom ss)

  ⇝*-pi-cod : ∀ {g d c c′} → _⇝*_ sig c c′ → _⇝*_ sig (tm-pi g d c) (tm-pi g d c′)
  ⇝*-pi-cod ⇝*-refl = ⇝*-refl
  ⇝*-pi-cod (⇝*-step s ss) = ⇝*-step (ξ-pi-cod s) (⇝*-pi-cod ss)

  ⇝*-lam-dom : ∀ {g d d′ b} → _⇝*_ sig d d′ → _⇝*_ sig (tm-lam g d b) (tm-lam g d′ b)
  ⇝*-lam-dom ⇝*-refl = ⇝*-refl
  ⇝*-lam-dom (⇝*-step s ss) = ⇝*-step (ξ-lam-dom s) (⇝*-lam-dom ss)

  ⇝*-lam-body : ∀ {g d b b′} → _⇝*_ sig b b′ → _⇝*_ sig (tm-lam g d b) (tm-lam g d b′)
  ⇝*-lam-body ⇝*-refl = ⇝*-refl
  ⇝*-lam-body (⇝*-step s ss) = ⇝*-step (ξ-lam-body s) (⇝*-lam-body ss)

  ⇝*-app₁ : ∀ {f f′ a} → _⇝*_ sig f f′ → _⇝*_ sig (tm-app f a) (tm-app f′ a)
  ⇝*-app₁ ⇝*-refl = ⇝*-refl
  ⇝*-app₁ (⇝*-step s ss) = ⇝*-step (ξ-app₁ s) (⇝*-app₁ ss)

  ⇝*-app₂ : ∀ {f a a′} → _⇝*_ sig a a′ → _⇝*_ sig (tm-app f a) (tm-app f a′)
  ⇝*-app₂ ⇝*-refl = ⇝*-refl
  ⇝*-app₂ (⇝*-step s ss) = ⇝*-step (ξ-app₂ s) (⇝*-app₂ ss)

  ⇝*-let-ty : ∀ {g ty ty′ v b} → _⇝*_ sig ty ty′ → _⇝*_ sig (tm-let g ty v b) (tm-let g ty′ v b)
  ⇝*-let-ty ⇝*-refl = ⇝*-refl
  ⇝*-let-ty (⇝*-step s ss) = ⇝*-step (ξ-let-ty s) (⇝*-let-ty ss)

  ⇝*-let-val : ∀ {g ty v v′ b} → _⇝*_ sig v v′ → _⇝*_ sig (tm-let g ty v b) (tm-let g ty v′ b)
  ⇝*-let-val ⇝*-refl = ⇝*-refl
  ⇝*-let-val (⇝*-step s ss) = ⇝*-step (ξ-let s) (⇝*-let-val ss)

  ⇝*-let-body : ∀ {g ty v b b′} → _⇝*_ sig b b′ → _⇝*_ sig (tm-let g ty v b) (tm-let g ty v b′)
  ⇝*-let-body ⇝*-refl = ⇝*-refl
  ⇝*-let-body (⇝*-step s ss) = ⇝*-step (ξ-let-body s) (⇝*-let-body ss)

  ⇝*-case : ∀ {s s′ m brs} → _⇝*_ sig s s′ → _⇝*_ sig (tm-case s m brs) (tm-case s′ m brs)
  ⇝*-case ⇝*-refl = ⇝*-refl
  ⇝*-case (⇝*-step s ss) = ⇝*-step (ξ-case s) (⇝*-case ss)

  ⇝*-case-motive : ∀ {s m m′ brs} → _⇝*_ sig m m′ → _⇝*_ sig (tm-case s m brs) (tm-case s m′ brs)
  ⇝*-case-motive ⇝*-refl = ⇝*-refl
  ⇝*-case-motive (⇝*-step s ss) = ⇝*-step (ξ-case-motive s) (⇝*-case-motive ss)

  ⇝*-case-brs : ∀ {s m brs brs′} → _⇝*ᵇ_ sig brs brs′ → _⇝*_ sig (tm-case s m brs) (tm-case s m brs′)
  ⇝*-case-brs ⇝ᵇ-nil = ⇝*-refl
  ⇝*-case-brs (⇝ᵇ-cons s ss) = ⇝*-step (ξ-case-brs (⇝ᵇ-cons s ss)) ⇝*-refl

  ⇝*-effect_type : ∀ {t t′} → _⇝*_ sig t t′ → _⇝*_ sig (tm-effect_type t) (tm-effect_type t′)
  ⇝*-effect_type ⇝*-refl = ⇝*-refl
  ⇝*-effect_type (⇝*-step s ss) = ⇝*-step (ξ-effect_type s) (⇝*-effect_type ss)

  ⇝*-effect_pure : ∀ {t t′} → _⇝*_ sig t t′ → _⇝*_ sig (tm-effect_pure t) (tm-effect_pure t′)
  ⇝*-effect_pure ⇝*-refl = ⇝*-refl
  ⇝*-effect_pure (⇝*-step s ss) = ⇝*-step (ξ-effect_pure s) (⇝*-effect_pure ss)

  ⇝*-effect_bind₁ : ∀ {e e′ k} → _⇝*_ sig e e′ → _⇝*_ sig (tm-effect_bind e k) (tm-effect_bind e′ k)
  ⇝*-effect_bind₁ ⇝*-refl = ⇝*-refl
  ⇝*-effect_bind₁ (⇝*-step s ss) = ⇝*-step (ξ-effect_bind₁ s) (⇝*-effect_bind₁ ss)

  ⇝*-effect_bind₂ : ∀ {e k k′} → _⇝*_ sig k k′ → _⇝*_ sig (tm-effect_bind e k) (tm-effect_bind e k′)
  ⇝*-effect_bind₂ ⇝*-refl = ⇝*-refl
  ⇝*-effect_bind₂ (⇝*-step s ss) = ⇝*-step (ξ-effect_bind₂ s) (⇝*-effect_bind₂ ss)

  -- Updating a spine element with its own value is the identity.
  setAt-id : ∀ {xs} (i : Fin (len xs)) → setAt xs i (lookupAt xs i) ≡ xs
  setAt-id {xs = y ∷ ys} zero = refl
  setAt-id {xs = y ∷ ys} (suc i) = cong (y ∷_) (setAt-id {xs = ys} i)

  -- Associativity of `_++_` (for the prefix accumulator).
  ++-assoc : ∀ (xs ys zs : List Term) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  -- Updating does not change the length.
  len-setAt : ∀ {xs} (i : Fin (len xs)) {x′} → len (setAt xs i x′) ≡ len xs
  len-setAt {xs = y ∷ ys} zero = refl
  len-setAt {xs = y ∷ ys} (suc i) = cong suc (len-setAt {xs = ys} i)

  -- Two updates at the same position compose (the later wins). The index is
  -- re-typed for the updated spine via `cast` (the length is unchanged).
  setAt-setAt : ∀ {xs} (i : Fin (len xs)) {x′ x″}
              → setAt (setAt xs i x′) (cast (sym (len-setAt i)) i) x″
              ≡ setAt xs i x″
  setAt-setAt {xs = y ∷ ys} zero = refl
  setAt-setAt {xs = y ∷ ys} (suc i) = cong (y ∷_) (setAt-setAt {xs = ys} i)

  -- Looking up the element just updated gives the new value.
  lookup-setAt : ∀ {xs} (i : Fin (len xs)) {u}
                  → lookupAt (setAt xs i u) (cast (sym (len-setAt i)) i) ≡ u
  lookup-setAt {xs = y ∷ ys} zero = refl
  lookup-setAt {xs = y ∷ ys} (suc i) = lookup-setAt {xs = ys} i

  -- Rewrite the SOURCE of a multi-step reduction along an equation.
  ⇝*-source : ∀ {t t′ u} → t ≡ u → _⇝*_ sig t t′ → _⇝*_ sig u t′
  ⇝*-source refl r = r

  -- `pre ++ x ∷ zs ≡ (pre ++ x ∷ []) ++ zs`.
  ++-left-cons : ∀ (pre : List Term) (x : Term) (zs : List Term)
               → pre ++ x ∷ zs ≡ (pre ++ x ∷ []) ++ zs
  ++-left-cons [] x zs = refl
  ++-left-cons (z ∷ zs) x ys = cong (z ∷_) (++-left-cons zs x ys)

  -- The position of the head of `args` in `pre ++ args`. The `args` argument
  -- is explicit so the empty-prefix case can see that `args` is non-empty.
  prefix-index : ∀ (pre : List Term) {x xs} → Fin (len (pre ++ x ∷ xs))
  prefix-index [] = zero
  prefix-index (z ∷ zs) = suc (prefix-index zs)

  -- `lookupAt (pre ++ x ∷ xs) (prefix-index pre) ≡ x`.
  lookup-prefix-index : ∀ (pre : List Term) {x xs}
                      → lookupAt (pre ++ x ∷ xs) (prefix-index pre) ≡ x
  lookup-prefix-index [] = refl
  lookup-prefix-index (z ∷ zs) = lookup-prefix-index zs

  -- `setAt (pre ++ x ∷ xs) (prefix-index pre) x′ ≡ pre ++ x′ ∷ xs`.
  setAt-prefix-index : ∀ (pre : List Term) {x xs x′}
                        → setAt (pre ++ x ∷ xs) (prefix-index pre) x′
                        ≡ pre ++ x′ ∷ xs
  setAt-prefix-index [] = refl
  setAt-prefix-index (z ∷ zs) = cong (z ∷_) (setAt-prefix-index zs)

  -- Termination: the `⇝*-at-*` helpers recurse on the multi-step reduction
  -- `ss`, which is structurally smaller at each call. Agda cannot see this
  -- because the SPINE argument is re-indexed by `setAt` (which preserves the
  -- length but is not a subterm), so we mark the block terminating with the
  -- recursion-on-`ss` justification.
  {-# TERMINATING #-}
  mutual
    ⇉→⇝* : ∀ {t t′} → _⇉_ t t′ → _⇝*_ sig t t′
    ⇉→⇝* p-type = ⇝*-refl
    ⇉→⇝* p-var = ⇝*-refl
    ⇉→⇝* p-global = ⇝*-refl
    ⇉→⇝* p-int_type = ⇝*-refl
    ⇉→⇝* p-int_lit = ⇝*-refl
    ⇉→⇝* p-nat_lit = ⇝*-refl
    ⇉→⇝* p-bounded_lit = ⇝*-refl
    ⇉→⇝* p-float_type = ⇝*-refl
    ⇉→⇝* p-float_lit = ⇝*-refl
    ⇉→⇝* p-binary_type = ⇝*-refl
    ⇉→⇝* p-atom_type = ⇝*-refl
    ⇉→⇝* p-atom_lit = ⇝*-refl
    ⇉→⇝* p-hole = ⇝*-refl
    ⇉→⇝* p-absurd = ⇝*-refl
    ⇉→⇝* (p-pi sd sc) =
      ⇝*-trans (⇝*-pi-dom (⇉→⇝* sd)) (⇝*-pi-cod (⇉→⇝* sc))
    ⇉→⇝* (p-lam sd sb) =
      ⇝*-trans (⇝*-lam-dom (⇉→⇝* sd)) (⇝*-lam-body (⇉→⇝* sb))
    ⇉→⇝* (p-let sty sv sb) =
      ⇝*-trans (⇝*-let-ty (⇉→⇝* sty))
        (⇝*-trans (⇝*-let-val (⇉→⇝* sv)) (⇝*-let-body (⇉→⇝* sb)))
    ⇉→⇝* (p-app sf sa) =
      ⇝*-trans (⇝*-app₁ (⇉→⇝* sf)) (⇝*-app₂ (⇉→⇝* sa))
    ⇉→⇝* (p-data sps sis) =
      ⇝*-trans (⇉→⇝*-spine-params [] _ _ sps) (⇉→⇝*-spine-indices [] _ _ sis)
    ⇉→⇝* (p-ctor sargs) = ⇉→⇝*-spine-ctor [] _ _ sargs
    ⇉→⇝* (p-ctor-head {x = x} {x′ = x′} {xs = xs} sx) = ⇝*-at-ctor (x ∷ xs) zero (⇉→⇝* sx)
    ⇉→⇝* (p-ctor-tail {x = x} {xs = xs} {xs′ = xs′} st) = ⇝*-ctor-tail-shift x (⇉→⇝* st)
    ⇉→⇝* (p-case ss sm sbs) =
      ⇝*-trans (⇝*-case (⇉→⇝* ss))
        (⇝*-trans (⇝*-case-motive (⇉→⇝* sm)) (⇝*-case-brs (⇉→⇝*-brs sbs)))
    ⇉→⇝* (p-effect_type st) = ⇝*-effect_type (⇉→⇝* st)
    ⇉→⇝* (p-effect_pure st) = ⇝*-effect_pure (⇉→⇝* st)
    ⇉→⇝* (p-effect_bind se sk) =
      ⇝*-trans (⇝*-effect_bind₁ (⇉→⇝* se)) (⇝*-effect_bind₂ (⇉→⇝* sk))
    ⇉→⇝* (p-β {g} {d} {d′} {b} {b′} {a} {a′} va va′ sd sb sa) =
      ⇝*-trans (⇝*-app₂ (⇉→⇝* sa))
        (⇝*-trans (⇝*-app₁ (⇝*-trans (⇝*-lam-dom (⇉→⇝* sd))
                                      (⇝*-lam-body (⇉→⇝* sb))))
          (⇝*-step (β va′) ⇝*-refl))
    ⇉→⇝* (p-ζ {g} {ty} {ty′} {v} {v′} {b} {b′} vv vv′ sty sv sb) =
      ⇝*-trans (⇝*-let-ty (⇉→⇝* sty))
        (⇝*-trans (⇝*-let-val (⇉→⇝* sv))
          (⇝*-trans (⇝*-let-body (⇉→⇝* sb)) (⇝*-step (ζ vv′) ⇝*-refl)))
    ⇉→⇝* (p-ι {m} {m′} {brs} {c} {ar} {b} {args} {args′} found len sm sargs) =
      ⇝*-trans (⇝*-case (⇉→⇝*-spine-ctor [] _ _ sargs))
               (⇝*-step (ι found (trans (⇉-terms-length sargs) len)) ⇝*-refl)
    ⇉→⇝* (p-ι-nat-zero {m} {m′} {brs} {ar} {b} found sm) =
      ⇝*-step (ι-nat-zero found) ⇝*-refl
    ⇉→⇝* (p-ι-nat-suc {m} {m′} {brs} {ar} {b} {n} found sm) =
      ⇝*-step (ι-nat-suc found) ⇝*-refl
    ⇉→⇝* (p-ι-bounded-zero {m} {m′} {brs} {ar} {b} found sm) =
      ⇝*-step (ι-bounded-zero found) ⇝*-refl
    ⇉→⇝* (p-ι-bounded-suc {m} {m′} {brs} {ar} {b} {k} found sm) =
      ⇝*-step (ι-bounded-suc found) ⇝*-refl
    ⇉→⇝* (p-δ eq) = ⇝*-step (δ eq) ⇝*-refl

    -- Simulate a parallel spine reduction by `_⇝_` steps, element by element.
    --
    -- `pre` is the (concrete) already-processed prefix. The next element is at
    -- position `length pre`, so `ξ-ctor-at (prefix-index pre)` reduces it. The
    -- recursive call's spine differs from the goal only by `++`
    -- associativity, discharged by `spine-ctor-cast`.
    ⇉→⇝*-spine-ctor : ∀ {c} (pre args args′ : List Term) → _⇉*ᵗ_ args args′
                    → _⇝*_ sig (tm-ctor c (pre ++ args)) (tm-ctor c (pre ++ args′))
    ⇉→⇝*-spine-ctor pre [] [] ⇉*-nil = ⇝*-refl
    ⇉→⇝*-spine-ctor {c} pre (x ∷ xs) (x′ ∷ xs′) (⇉*-cons {x} {x′} {xs} {xs′} sx sxs) =
      ⇝*-trans (⇝*-at-ctor (pre ++ x ∷ xs) (prefix-index pre)
                           (⇝*-source (sym (lookup-prefix-index pre)) (⇉→⇝* sx)))
               (spine-ctor-cast c pre x x′ xs xs′ (⇉→⇝*-spine-ctor (pre ++ x′ ∷ []) xs xs′ sxs))

    -- `ξ-ctor-at` iterated over a multi-step reduction of the element at `i`.
    ⇝*-at-ctor : ∀ {c} (xs : List Term) (i : Fin (len xs)) {x′}
               → _⇝*_ sig (lookupAt xs i) x′
               → _⇝*_ sig (tm-ctor c xs) (tm-ctor c (setAt xs i x′))
    ⇝*-at-ctor {c} xs i ⇝*-refl =
      subst (λ zs → _⇝*_ sig (tm-ctor c xs) (tm-ctor c zs)) (sym (setAt-id i)) ⇝*-refl
    ⇝*-at-ctor {c} xs i {x′} (⇝*-step {u = u} s ss) =
      ⇝*-trans (⇝*-step (ξ-ctor-at i s) ⇝*-refl)
               (subst (λ zs → _⇝*_ sig (tm-ctor c (setAt xs i u)) (tm-ctor c zs))
                      (setAt-setAt {xs = xs} i {x′ = u} {x″ = x′})
                      (⇝*-at-ctor (setAt xs i u) (cast (sym (len-setAt i)) i)
                                  (⇝*-source (sym (lookup-setAt {xs = xs} i {u = u})) ss)))

    -- Lift a multi-step constructor reduction into the tail position.
    ⇝*-ctor-tail-shift : ∀ {c} (x : Term) {xs xs′}
                       → _⇝*_ sig (tm-ctor c xs) (tm-ctor c xs′)
                       → _⇝*_ sig (tm-ctor c (x ∷ xs)) (tm-ctor c (x ∷ xs′))
    ⇉→⇝*-brs : ∀ {bs bs′} → _⇉*ᵇ_ bs bs′ → _⇝*ᵇ_ sig bs bs′
    ⇉→⇝*-brs ⇉ᵇ-nil = ⇝ᵇ-nil
    ⇉→⇝*-brs (⇉ᵇ-cons sbs sbs′) = ⇝ᵇ-cons (⇉→⇝*-star sbs) (⇉→⇝*-brs sbs′)

    ⇉→⇝*-star : ∀ {t t′} → _⇉*_ t t′ → _⇝*_ sig t t′
    ⇉→⇝*-star ⇉*-refl = ⇝*-refl
    ⇉→⇝*-star (⇉*-step s ss) = ⇝*-trans (⇉→⇝* s) (⇉→⇝*-star ss)

    ⇝*-ctor-tail-shift x ⇝*-refl = ⇝*-refl
    ⇝*-ctor-tail-shift {c} x (⇝*-step (ξ-ctor-at i s) ss) =
      ⇝*-trans (⇝*-step (ξ-ctor-at (suc i) s) ⇝*-refl) (⇝*-ctor-tail-shift x ss)

    -- Reduce a constructor's tail (the head is fixed) via `ξ-ctor-at` at
    -- position 0 of the tail. Mirrors the parallel `p-ctor-tail` rule.
    ⇝*-ctor-tail : ∀ {c} (pre : List Term) {xs xs′}
                 → _⇉*ᵗ_ xs xs′
                 → _⇝*_ sig (tm-ctor c (pre ++ xs)) (tm-ctor c (pre ++ xs′))
    ⇝*-ctor-tail pre ⇉*-nil = ⇝*-refl
    ⇝*-ctor-tail {c} pre (⇉*-cons {x = y} {x′ = y′} {xs = ys} {xs′ = ys′} sy sys) =
      ⇝*-trans (⇝*-at-ctor (pre ++ y ∷ ys) (prefix-index pre) (⇝*-source (sym (lookup-prefix-index pre)) (⇉→⇝* sy)))
               (spine-ctor-cast c pre y y′ ys ys′ (⇝*-ctor-tail (pre ++ y′ ∷ []) sys))

    -- The `++`/`setAt` bookkeeping for one spine step, isolated.
    -- `x` is the ORIGINAL element at the position (so the `setAt` in the
    -- argument type matches what `⇝*-at-ctor` produces).
    spine-ctor-cast : ∀ (c : Name) (pre : List Term) (x x′ : Term) (xs xs′ : List Term)
                    → _⇝*_ sig (tm-ctor c ((pre ++ x′ ∷ []) ++ xs))
                               (tm-ctor c ((pre ++ x′ ∷ []) ++ xs′))
                    → _⇝*_ sig (tm-ctor c (setAt (pre ++ x ∷ xs) (prefix-index pre) x′))
                               (tm-ctor c (pre ++ x′ ∷ xs′))
    spine-ctor-cast c pre x x′ xs xs′ rec =
      subst (λ zs → _⇝*_ sig (tm-ctor c zs) (tm-ctor c (pre ++ x′ ∷ xs′)))
            (sym (setAt-prefix-index pre))
            (subst (λ zs → _⇝*_ sig (tm-ctor c zs) (tm-ctor c (pre ++ x′ ∷ xs′)))
                   (sym (++-left-cons pre x′ xs))
                   (subst (λ zs → _⇝*_ sig (tm-ctor c ((pre ++ x′ ∷ []) ++ xs)) (tm-ctor c zs))
                          (sym (++-left-cons pre x′ xs′))
                          rec))

    ⇝*-at-params : ∀ {n is} (ps : List Term) (i : Fin (len ps)) {x′}
                 → _⇝*_ sig (lookupAt ps i) x′
                 → _⇝*_ sig (tm-data n ps is) (tm-data n (setAt ps i x′) is)
    ⇝*-at-params {n} {is} ps i ⇝*-refl =
      subst (λ zs → _⇝*_ sig (tm-data n ps is) (tm-data n zs is)) (sym (setAt-id i)) ⇝*-refl
    ⇝*-at-params {n} {is} ps i {x′} (⇝*-step {u = u} s ss) =
      ⇝*-trans (⇝*-step (ξ-data-params-at i s) ⇝*-refl)
               (subst (λ zs → _⇝*_ sig (tm-data n (setAt ps i u) is) (tm-data n zs is))
                      (setAt-setAt {xs = ps} i {x′ = u} {x″ = x′})
                      (⇝*-at-params (setAt ps i u) (cast (sym (len-setAt i)) i)
                                    (⇝*-source (sym (lookup-setAt {xs = ps} i {u = u})) ss)))

    ⇝*-at-indices : ∀ {n ps} (is : List Term) (i : Fin (len is)) {x′}
                  → _⇝*_ sig (lookupAt is i) x′
                  → _⇝*_ sig (tm-data n ps is) (tm-data n ps (setAt is i x′))
    ⇝*-at-indices {n} {ps} is i ⇝*-refl =
      subst (λ zs → _⇝*_ sig (tm-data n ps is) (tm-data n ps zs)) (sym (setAt-id i)) ⇝*-refl
    ⇝*-at-indices {n} {ps} is i {x′} (⇝*-step {u = u} s ss) =
      ⇝*-trans (⇝*-step (ξ-data-indices-at i s) ⇝*-refl)
               (subst (λ zs → _⇝*_ sig (tm-data n ps (setAt is i u)) (tm-data n ps zs))
                      (setAt-setAt {xs = is} i {x′ = u} {x″ = x′})
                      (⇝*-at-indices (setAt is i u) (cast (sym (len-setAt i)) i)
                                     (⇝*-source (sym (lookup-setAt {xs = is} i {u = u})) ss)))

    ⇉→⇝*-spine-params : ∀ {n is} (pre ps ps′ : List Term) → _⇉*ᵗ_ ps ps′
                      → _⇝*_ sig (tm-data n (pre ++ ps) is) (tm-data n (pre ++ ps′) is)
    ⇉→⇝*-spine-params pre [] [] ⇉*-nil = ⇝*-refl
    ⇉→⇝*-spine-params pre (x ∷ xs) (x′ ∷ xs′) (⇉*-cons {x} {x′} {xs} {xs′} sx sxs) =
      ⇝*-trans (⇝*-at-params (pre ++ x ∷ xs) (prefix-index pre)
                             (⇝*-source (sym (lookup-prefix-index pre)) (⇉→⇝* sx)))
               (spine-params-cast pre x x′ xs xs′ (⇉→⇝*-spine-params (pre ++ x′ ∷ []) xs xs′ sxs))

    spine-params-cast : ∀ {n is} (pre : List Term) (x x′ : Term) (xs xs′ : List Term)
                      → _⇝*_ sig (tm-data n ((pre ++ x′ ∷ []) ++ xs) is)
                                 (tm-data n ((pre ++ x′ ∷ []) ++ xs′) is)
                      → _⇝*_ sig (tm-data n (setAt (pre ++ x ∷ xs) (prefix-index pre) x′) is)
                                 (tm-data n (pre ++ x′ ∷ xs′) is)
    spine-params-cast pre x x′ xs xs′ rec =
      subst (λ zs → _⇝*_ sig (tm-data _ zs _) (tm-data _ (pre ++ x′ ∷ xs′) _))
            (sym (setAt-prefix-index pre))
            (subst (λ zs → _⇝*_ sig (tm-data _ zs _) (tm-data _ (pre ++ x′ ∷ xs′) _))
                   (sym (++-left-cons pre x′ xs))
                   (subst (λ zs → _⇝*_ sig (tm-data _ ((pre ++ x′ ∷ []) ++ xs) _) (tm-data _ zs _))
                          (sym (++-left-cons pre x′ xs′))
                          rec))

    ⇉→⇝*-spine-indices : ∀ {n ps} (pre is is′ : List Term) → _⇉*ᵗ_ is is′
                       → _⇝*_ sig (tm-data n ps (pre ++ is)) (tm-data n ps (pre ++ is′))
    ⇉→⇝*-spine-indices pre [] [] ⇉*-nil = ⇝*-refl
    ⇉→⇝*-spine-indices pre (x ∷ xs) (x′ ∷ xs′) (⇉*-cons {x} {x′} {xs} {xs′} sx sxs) =
      ⇝*-trans (⇝*-at-indices (pre ++ x ∷ xs) (prefix-index pre)
                              (⇝*-source (sym (lookup-prefix-index pre)) (⇉→⇝* sx)))
               (spine-indices-cast pre x x′ xs xs′ (⇉→⇝*-spine-indices (pre ++ x′ ∷ []) xs xs′ sxs))

    spine-indices-cast : ∀ {n ps} (pre : List Term) (x x′ : Term) (xs xs′ : List Term)
                       → _⇝*_ sig (tm-data n ps ((pre ++ x′ ∷ []) ++ xs))
                                  (tm-data n ps ((pre ++ x′ ∷ []) ++ xs′))
                       → _⇝*_ sig (tm-data n ps (setAt (pre ++ x ∷ xs) (prefix-index pre) x′))
                                  (tm-data n ps (pre ++ x′ ∷ xs′))
    spine-indices-cast pre x x′ xs xs′ rec =
      subst (λ zs → _⇝*_ sig (tm-data _ _ zs) (tm-data _ _ (pre ++ x′ ∷ xs′)))
            (sym (setAt-prefix-index pre))
            (subst (λ zs → _⇝*_ sig (tm-data _ _ zs) (tm-data _ _ (pre ++ x′ ∷ xs′)))
                   (sym (++-left-cons pre x′ xs))
                   (subst (λ zs → _⇝*_ sig (tm-data _ _ ((pre ++ x′ ∷ []) ++ xs)) (tm-data _ _ zs))
                          (sym (++-left-cons pre x′ xs′))
                          rec))
