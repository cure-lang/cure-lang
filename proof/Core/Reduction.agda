------------------------------------------------------------------------
-- The dynamic semantics: the reduction relation ⇝.
--
-- This is the SPECIFICATION of Core evaluation, not the NbE implementation.
-- docs/SOUNDNESS.md §1.3 names four rules:
--
--   β: (λx. b) a ⇝ b[x := a]
--   ζ: let x = v in b ⇝ b[x := v]
--   ι: case (ctor c args) of … ⇝ b_c[args]
--   δ: global f ⇝ body(f)   — GATED on a totality certificate
--
-- We define ⇝ as an inductive family (a small-step relation), which is what
-- Progress and Preservation are stated over. Modelling the relation rather
-- than the NbE function sidesteps the termination obligations of a total
-- evaluator (the kernel's own `Eval` is partial by design: it can raise on
-- ill-typed terms) and matches the theorem statement exactly.
--
-- Congruence (reduction under a context) is given by the `ξ-*` rules, which
-- mirror where the kernel forces subterms: tm-app` forces the function
-- position, tm-case` forces the scrutinee, and the inert effect nodes force
-- their subterms structurally.
------------------------------------------------------------------------
module Core.Reduction where

open import Data.Bool using (Bool; true; false)
open import Data.String using (_==_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; length; map; find)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax

------------------------------------------------------------------------
-- Substituting a list of constructor arguments into a branch body.
--
-- The branch binds `arity` fields; `args` are the fields in surface order.
-- The LAST field is de Bruijn 0 (matching `Eval.reduce_branch_body`, which
-- binds `reverse(fields) ++ base_env`). We substitute field i at index
-- `arity - 1 - i`, then shift the remaining args as we descend.
------------------------------------------------------------------------

substArgs : List Term → Term → Term
substArgs [] b = b
substArgs (a ∷ as) b = substArgs as (substT (length as) a b)

------------------------------------------------------------------------
-- The δ-table: a signature mapping certified global names to their bodies.
--
-- The kernel gates δ on a totality certificate (`Env.certified?`). We
-- model the certified fragment as a finite map from names to bodies; a
-- name NOT in the map is an opaque global that never unfolds (it reduces
-- to a neutral, per `Eval.eval({:global, name})`).
--
-- This is the single hypothesis the whole soundness argument rests on
-- (docs/SOUNDNESS.md §5.3(2), §7.2): we will later attach the *property*
-- that every body in this table terminates, but Progress/Preservation
-- only need the table to be well-typed (Preservation §4, δ case).
------------------------------------------------------------------------

record Signature : Set where
  field
    body : Name → Maybe Term
    -- The declared type of each global (for the δ Preservation case).
    type-of : Name → Maybe Term

open Signature public

------------------------------------------------------------------------
-- Branch lookup: find the branch for a constructor name.
------------------------------------------------------------------------

findBranch : Name → List Branch → Maybe Branch
findBranch c [] = nothing
findBranch c ((cn , ar , b) ∷ xs) with c == cn
... | true  = just (cn , ar , b)
... | false = findBranch c xs

------------------------------------------------------------------------
-- The reduction relation, parameterised by the signature.
------------------------------------------------------------------------

module _ (sig : Signature) where

  infix 4 _⇝_

  mutual

    data _⇝_ : Term → Term → Set where

      -- β: (λx. b) a ⇝ b[x := a]
      β : ∀ {g d b a} → tm-app (tm-lam g d b) a ⇝ substT 0 a b

      -- ζ: let x = v in b ⇝ b[x := v]
      ζ : ∀ {g ty v b} → tm-let g ty v b ⇝ substT 0 v b

      -- ι: case (ctor c args) of … ⇝ b_c[args]
      -- The branch body lives under `arity` binders; we substitute the fields
      -- in left-to-right, innermost last, matching `Eval.reduce_branch_body`.
      ι : ∀ {m brs c ar b args}
        → findBranch c brs ≡ just (c , ar , b)
        → length args ≡ ar
        → tm-case (tm-ctor c args) m brs ⇝ substArgs args b

      -- δ: global f ⇝ body(f), only when the signature supplies a body.
      δ : ∀ {f body′} → Signature.body sig f ≡ just body′ → tm-global f ⇝ body′

      -- Congruence: application forces the function position.
      ξ-app₁ : ∀ {f f′ a} → f ⇝ f′ → tm-app f a ⇝ tm-app f′ a

      -- Congruence: application forces the argument once the function is a value.
      ξ-app₂ : ∀ {f a a′} → a ⇝ a′ → tm-app f a ⇝ tm-app f a′

      -- Congruence: case forces the scrutinee.
      ξ-case : ∀ {s s′ m brs} → s ⇝ s′ → tm-case s m brs ⇝ tm-case s′ m brs

      -- Congruence: case motive.
      ξ-case-motive : ∀ {s m m′ brs} → m ⇝ m′ → tm-case s m brs ⇝ tm-case s m′ brs

      -- Congruence: inert effect nodes reduce their subterms structurally.
      ξ-effect_type : ∀ {t t′} → t ⇝ t′ → tm-effect_type t ⇝ tm-effect_type t′
      ξ-effect_pure : ∀ {t t′} → t ⇝ t′ → tm-effect_pure t ⇝ tm-effect_pure t′
      ξ-effect_bind₁ : ∀ {e e′ k} → e ⇝ e′ → tm-effect_bind e k ⇝ tm-effect_bind e′ k
      ξ-effect_bind₂ : ∀ {e k k′} → k ⇝ k′ → tm-effect_bind e k ⇝ tm-effect_bind e k′

      -- Congruence: let forces its value.
      ξ-let : ∀ {g ty v v′ b} → v ⇝ v′ → tm-let g ty v b ⇝ tm-let g ty v′ b

      -- Congruence: constructors force their arguments (one at a time).
      ξ-ctor : ∀ {n xs ys x y} → x ⇝ y → xs ⇝*ᵗ ys → tm-ctor n (x ∷ xs) ⇝ tm-ctor n (y ∷ ys)

      -- Congruence: data spines force their arguments.
      ξ-data-params : ∀ {n xs ys is} → xs ⇝*ᵗ ys → tm-data n xs is ⇝ tm-data n ys is
      ξ-data-indices : ∀ {n ps xs ys} → xs ⇝*ᵗ ys → tm-data n ps xs ⇝ tm-data n ps ys

      -- Congruence: Π/λ force their domain (the codomain/body are under a binder).
      ξ-pi-dom : ∀ {g d d′ b} → d ⇝ d′ → tm-pi g d b ⇝ tm-pi g d′ b
      ξ-lam-dom : ∀ {g d d′ b} → d ⇝ d′ → tm-lam g d b ⇝ tm-lam g d′ b

      -- Congruence: Π/λ bodies reduce under the binder.
      ξ-pi-cod : ∀ {g d b b′} → b ⇝ b′ → tm-pi g d b ⇝ tm-pi g d b′
      ξ-lam-body : ∀ {g d b b′} → b ⇝ b′ → tm-lam g d b ⇝ tm-lam g d b′

    data _⇝*ᵗ_ : List Term → List Term → Set where
      ⇝*-nil  : [] ⇝*ᵗ []
      ⇝*-cons : ∀ {x x′ xs xs′} → x ⇝ x′ → xs ⇝*ᵗ xs′ → (x ∷ xs) ⇝*ᵗ (x′ ∷ xs′)

  ------------------------------------------------------------------------
  -- Multi-step reduction: the reflexive-transitive closure.
  ------------------------------------------------------------------------

  infix 4 _⇝*_

  data _⇝*_ : Term → Term → Set where
    ⇝*-refl  : ∀ {t} → t ⇝* t
    ⇝*-step  : ∀ {t u v} → t ⇝ u → u ⇝* v → t ⇝* v
