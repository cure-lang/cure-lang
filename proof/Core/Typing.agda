------------------------------------------------------------------------
-- The typing judgment: bidirectional infer/check.
--
-- Faithful to `Cure.Core.Kernel` (lib/cure/core/kernel.ex):
--
--   infer(Γ, e) = {:ok, T}   — synthesise the type T
--   check(Γ, e, T) = :ok     — verify e against the expected type T,
--                              falling back to infer plus a cumulative
--                              conversion test (`check_via_infer`).
--
-- We write `Γ ⊢ e ⇒ T` for infer and `Γ ⊢ e ⇐ T` for check, where `Γ` is a
-- context (a telescope of types) and `T` is a syntactic type (a Term).
--
-- Types are compared by the conversion relation `_≈_` (Core/Conv.agda),
-- which is the syntactic counterpart of the kernel's NbE definitional
-- equality. Cumulativity is applied at the sort level: `Type i <: Type j`
-- when `i ≤ j`.
--
-- The context is a list of types, most-recent first (de Bruijn index 0 at
-- the head), matching `Cure.Core.Context`.
------------------------------------------------------------------------
module Core.Typing where

open import Data.Bool using (Bool; true; false)
open import Data.String using (_==_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_; _≤ᵇ_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade; erased; linear; affine; unrestricted)
open import Core.Universe using (Level; l0; l1; l2; InRange; in-range;
                                  toNat; ceiling; succLevel;
                                  _≤ˡ_; l≤-refl; l0≤l1; l0≤l2; l1≤l2; ≤ˡ-trans;
                                  _⊔ˡ_; ⊔ˡ-left; ⊔ˡ-right)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature; body; type-of)

------------------------------------------------------------------------
-- Pointwise list relation
------------------------------------------------------------------------

data All2 {A : Set} (R : A → A → Set) : List A → List A → Set where
  a2[] : All2 R [] []
  a2∷  : ∀ {x y xs ys} → R x y → All2 R xs ys → All2 R (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Contexts
--
-- A context is a telescope of types, most-recent first. `Γ ∋ T` is the
-- lookup judgment: variable `k` has type `T` in `Γ`.
------------------------------------------------------------------------

-- A context is a telescope of types, most-recent first. Indexing by length
-- (rather than a bare list) makes variable lookup a total FUNCTION on
-- `Fin n`, which is what makes the weakening and substitution lemmas
-- clean: the de Bruijn bookkeeping becomes a `refl`-level identity rather
-- than an inductive relation to be inverted.
--
-- The context stores types in the GLOBAL de Bruijn convention: prepending
-- a binder renames every existing type by `wk` (`wk k = suc k`), so that a
-- type's free variables keep referring to the same binders. This is what
-- makes weakening's term operation (`rename wk`) and its context operation
-- (`extend`) agree, which is the crux of the de Bruijn bookkeeping.
data Context : Set where
  ⟨⟩  : Context
  _▷_ : Context → Term → Context

-- The length of a context.
lengthCtx : Context → ℕ
lengthCtx ⟨⟩ = 0
lengthCtx (Γ ▷ T) = suc (lengthCtx Γ)

-- Variable lookup: a `Fin (lengthCtx Γ)` into a context gives the type of
-- that variable. Index 0 is the most-recently-bound variable (the head).
-- This is a total function, mirroring the kernel's `Context.lookup(ctx, k)`.
lookup : (Γ : Context) → Fin (lengthCtx Γ) → Term
lookup (Γ ▷ T) zero = T
lookup (Γ ▷ T) (suc i) = lookup Γ i

-- The weakening renaming: shift every index up by one.
wk : Ren
wk k = suc k

-- Rename every type in a context.
renameCtx : Ren → Context → Context
renameCtx ρ ⟨⟩ = ⟨⟩
renameCtx ρ (Γ ▷ T) = renameCtx ρ Γ ▷ rename ρ T

-- Context extension: prepend a fresh binder, renaming every existing type
-- by `wk` (the global de Bruijn convention). This keeps a stored type's
-- free variables referring to the same binders after the prepend, which is
-- what makes the substitution lemma's `⇒-var` cases go through.
extend : Context → Term → Context
extend Γ T = renameCtx wk Γ ▷ T

-- `lengthCtx (renameCtx ρ Γ) ≡ lengthCtx Γ`.
length-renameCtx : ∀ ρ Γ → lengthCtx (renameCtx ρ Γ) ≡ lengthCtx Γ
length-renameCtx ρ ⟨⟩ = refl
length-renameCtx ρ (Γ ▷ T) = cong suc (length-renameCtx ρ Γ)

-- `lengthCtx (extend Γ T) ≡ suc (lengthCtx Γ)`.
length-extend : ∀ Γ T → lengthCtx (extend Γ T) ≡ suc (lengthCtx Γ)
length-extend Γ T = cong suc (length-renameCtx wk Γ)

-- `subst Fin refl i ≡ i`.
subst-refl : ∀ {n} (i : Fin n) → subst Fin refl i ≡ i
subst-refl i = refl

-- `subst Fin (sym (cong suc p)) zero ≡ zero`.
subst-fin-zero : ∀ {n m : ℕ} (p : m ≡ n) → subst Fin (sym (cong suc p)) zero ≡ zero
subst-fin-zero refl = refl

-- `subst Fin (sym (cong suc p)) (suc i) ≡ suc (subst Fin (sym p) i)`.
subst-fin-suc : ∀ {n m : ℕ} (p : m ≡ n) (i : Fin n)
              → subst (λ k → Fin k) (sym (cong {A = ℕ} suc p)) (suc i)
              ≡ suc (subst (λ k → Fin k) (sym p) i)
subst-fin-suc refl i = cong suc (subst-refl i)



-- Weakening: a `Fin (lengthCtx Γ)` embeds into `Fin (lengthCtx (extend Γ T))`.
wkFin : ∀ Γ T → Fin (lengthCtx Γ) → Fin (lengthCtx (extend Γ T))
wkFin Γ T i = subst (λ n → Fin n) (sym (length-extend Γ T)) (suc i)

-- Looking up a renamed context, stated with the index in the original
-- context and the length transport applied to the index.
lookup-renameCtx : ∀ {Γ} ρ (i : Fin (lengthCtx Γ))
                 → lookup (renameCtx ρ Γ) (subst (λ n → Fin n) (sym (length-renameCtx ρ Γ)) i) ≡ rename ρ (lookup Γ i)
lookup-renameCtx {⟨⟩} ρ ()
lookup-renameCtx {Γ ▷ T} ρ zero = cong (lookup (renameCtx ρ (Γ ▷ T))) (subst-fin-zero (length-renameCtx ρ Γ))
lookup-renameCtx {Γ ▷ T} ρ (suc i) =
  trans (cong (lookup (renameCtx ρ (Γ ▷ T))) (subst-fin-suc (length-renameCtx ρ Γ) i))
        (lookup-renameCtx {Γ} ρ i)

-- The weakening lookup law: after extending, an existing variable is found
-- at the lifted index, with its type renamed by `wk`.
lookup-extend : ∀ {Γ} (T : Term) (i : Fin (lengthCtx Γ))
              → lookup (extend Γ T) (wkFin Γ T i) ≡ rename wk (lookup Γ i)
lookup-extend {Γ} T i =
  trans (cong (lookup (extend Γ T)) (subst-fin-suc (length-renameCtx wk Γ) i))
        (lookup-renameCtx wk i)

------------------------------------------------------------------------
-- Conversion (definitional equality)
--
-- We take `_≈_` as a parameter of the typing judgment — it is the
-- syntactic counterpart of the kernel's NbE conversion. In Core/Conv.agda
-- we will define it and prove its laws. Here we only need its interface.
--
-- Making it a record (rather than a bare relation) keeps the soundness
-- theorem honest about what it assumes: conversion is an equivalence that
-- is a congruence for the type formers the kernel's `Conv` implements.
------------------------------------------------------------------------

record Conversion : Set₁ where
  field
    _≈_        : Term → Term → Set
    ≈-refl     : ∀ {t} → t ≈ t
    ≈-sym      : ∀ {t u} → t ≈ u → u ≈ t
    ≈-trans    : ∀ {t u v} → t ≈ u → u ≈ v → t ≈ v
    -- Congruence for Π (the load-bearing case for Preservation's β rule).
    ≈-pi       : ∀ {g d d′ c c′} → d ≈ d′ → c ≈ c′ → tm-pi g d c ≈ tm-pi g d′ c′
    -- Congruence for application.
    ≈-app      : ∀ {f f′ a a′} → f ≈ f′ → a ≈ a′ → tm-app f a ≈ tm-app f′ a′
    -- Congruence for data/ctor spines.
    ≈-data     : ∀ {n ps ps′ is is′} → All2 _≈_ ps ps′ → All2 _≈_ is is′ → tm-data n ps is ≈ tm-data n ps′ is′
    ≈-ctor     : ∀ {n args args′} → All2 _≈_ args args′ → tm-ctor n args ≈ tm-ctor n args′
    -- Congruence for Effect.
    ≈-effect_type : ∀ {t t′} → t ≈ t′ → tm-effect_type t ≈ tm-effect_type t′
    ≈-effect_pure : ∀ {t t′} → t ≈ t′ → tm-effect_pure t ≈ tm-effect_pure t′
    ≈-effect_bind : ∀ {e e′ k k′} → e ≈ e′ → k ≈ k′ → tm-effect_bind e k ≈ tm-effect_bind e′ k′

open Conversion public

------------------------------------------------------------------------
-- The typing judgment
--
-- Parameterised by the inductive environment, the δ-signature, and the
-- conversion relation.
------------------------------------------------------------------------

module Typing (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open IndEnv ind
  open Signature sig
  open Conversion conv

  infix 4 _⊢_⇒_ _⊢_⇐_

  -- Bidirectional typing, mutually recursive (check falls back to infer).
  data _⊢_⇒_ : Context → Term → Term → Set
  data _⊢_⇐_ : Context → Term → Term → Set

  -- Spine checking: a list of terms against a dependent telescope.
  data _⊢*_⇐*_ : Context → List Term → Telescope → Set

  -- Branch checking: a list of branches against a family and its motive.
  data _⊢*brs_⇐*ᵇ_ : Context → List Branch → (Name × Term) → Set

  ------------------------------------------------------------------------
  -- Helpers
  ------------------------------------------------------------------------

  -- Extend a context by `n` fresh binders (the branch fields). The field
  -- types are not needed for the *positive* branch obligation; a later
  -- slice threads the constructor's argument telescope through here.
  extendⁿ : Context → ℕ → Context
  extendⁿ Γ zero = Γ
  extendⁿ Γ (suc n) = extendⁿ (extend Γ (tm-hole "field")) n

  -- The field variables bound by a branch of arity `ar`. The kernel binds
  -- the LAST field at index 0, so the field list is `[ar-1, …, 0]`.
  branch-field-vars : ℕ → List Term
  branch-field-vars ar = map tm-var (countdown ar)
    where
      countdown : ℕ → List ℕ
      countdown zero = []
      countdown (suc n) = n ∷ countdown n

  data _⊢_⇒_ where

    -- Type l : Type (l+1), when the successor is in range.
    ⇒-type : ∀ {Γ l l′} → succLevel l ≡ just l′
           → Γ ⊢ tm-type l ⇒ tm-type l′

    -- Variables: the type is the context's entry at the variable's index.
    ⇒-var : ∀ {Γ} (i : Fin (lengthCtx Γ))
          → Γ ⊢ tm-var (toℕ i) ⇒ lookup Γ i

    -- Π formation: dom : Type l1, cod : Type l2 under the binder, so
    -- Π lives at max(l1, l2).
    ⇒-pi : ∀ {Γ g d c l1 l2}
         → Γ ⊢ d ⇒ tm-type l1
         → extend Γ d ⊢ c ⇒ tm-type l2
         → Γ ⊢ tm-pi g d c ⇒ tm-type (l1 ⊔ˡ l2)

    -- λ inference: infer the domain's sort, infer the body's type, and
    -- form the Π type. (The kernel reifies the codomain via `Quote`; the
    -- syntactic presentation keeps the inferred body type directly.)
    ⇒-lam : ∀ {Γ g d b l T}
          → Γ ⊢ d ⇒ tm-type l
          → extend Γ d ⊢ b ⇒ T
          → Γ ⊢ tm-lam g d b ⇒ tm-pi g d T

    -- Application: infer the function type, require it to be a Π, check
    -- the argument against the domain, and return the codomain instantiated
    -- at the argument.
    ⇒-app : ∀ {Γ f a g d c}
          → Γ ⊢ f ⇒ tm-pi g d c
          → Γ ⊢ a ⇐ d
          → Γ ⊢ tm-app f a ⇒ substT 0 a c

    -- let (ζ-transparent): check the value against the ascription, then
    -- infer the body under a context extended with the value's type.
    ⇒-let : ∀ {Γ g ty v b l T}
          → Γ ⊢ ty ⇒ tm-type l
          → Γ ⊢ v ⇐ ty
          → extend Γ ty ⊢ b ⇒ T
          → Γ ⊢ tm-let g ty v b ⇒ T

    -- Global: look up the declared type in the signature.
    ⇒-global : ∀ {Γ f T} → Signature.type-of sig f ≡ just T → Γ ⊢ tm-global f ⇒ T

    -- Primitive base types live in Type 0.
    ⇒-int_type    : ∀ {Γ} → Γ ⊢ tm-int_type ⇒ tm-type l0
    ⇒-float_type  : ∀ {Γ} → Γ ⊢ tm-float_type ⇒ tm-type l0
    ⇒-binary_type : ∀ {Γ} → Γ ⊢ tm-binary_type ⇒ tm-type l0
    ⇒-atom_type   : ∀ {Γ} → Γ ⊢ tm-atom_type ⇒ tm-type l0

    -- Literals inhabit their base types.
    ⇒-int_lit   : ∀ {Γ k} → Γ ⊢ tm-int_lit k ⇒ tm-int_type
    ⇒-float_lit : ∀ {Γ} → Γ ⊢ tm-float_lit ⇒ tm-float_type
    ⇒-atom_lit  : ∀ {Γ n} → Γ ⊢ tm-atom_lit n ⇒ tm-atom_type

    -- Nat/Bounded literals inhabit their (builtin) families.
    ⇒-nat_lit     : ∀ {Γ n N} → IndEnv.builtins ind "nat" ≡ just N → Γ ⊢ tm-nat_lit n ⇒ tm-data N [] []
    ⇒-bounded_lit : ∀ {Γ k B} → IndEnv.builtins ind "bounded" ≡ just B → Γ ⊢ tm-bounded_lit k ⇒ tm-data B [] []

    -- Data formation: check the params and indices against the family's
    -- telescopes; the family lives at its declared level.
    ⇒-data : ∀ {Γ n ps is f}
           → findFamily n (IndEnv.families ind) ≡ just f
           → Γ ⊢* ps ⇐* fam-params f
           → Γ ⊢* is ⇐* fam-indices f
           → Γ ⊢ tm-data n ps is ⇒ tm-type (fam-level f)

    -- Constructor: check the args against the constructor's telescope and
    -- compute the result data type.
    ⇒-ctor : ∀ {Γ c args f ct}
           → findCtor c (IndEnv.families ind) ≡ just (f , ct)
           → Γ ⊢* args ⇐* ctor-args ct
           → Γ ⊢ tm-ctor c args ⇒ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)

    -- Dependent case: the scrutinee's type must be a data type; the motive
    -- must be a type family; every possible branch must be present and
    -- type-check against the motive instantiated at its constructor.
    --
    -- The result type is the motive applied to the scrutinee
    -- (`apply_motive` in the kernel).
    ⇒-case : ∀ {Γ s m brs n ps is T}
           → Γ ⊢ s ⇒ tm-data n ps is
           → Γ ⊢ m ⇒ T
           → Γ ⊢*brs brs ⇐*ᵇ (n , m)
           → Γ ⊢ tm-case s m brs ⇒ tm-app m s

    -- Inert effects: Effect(t) is level-preserving.
    ⇒-effect_type : ∀ {Γ t l} → Γ ⊢ t ⇒ tm-type l → Γ ⊢ tm-effect_type t ⇒ tm-type l
    ⇒-effect_pure : ∀ {Γ a A} → Γ ⊢ a ⇒ A → Γ ⊢ tm-effect_pure a ⇒ tm-effect_type A
    ⇒-effect_bind : ∀ {Γ e k A B}
                  → Γ ⊢ e ⇒ tm-effect_type A
                  → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type B)
                  → Γ ⊢ tm-effect_bind e k ⇒ tm-effect_type B

    -- A hole has no inference rule (it is checkable at any type).
    -- {:absurd} is rejected in reachable position (no inference rule).

  -- Checking judgment.
  data _⊢_⇐_ where

    -- A λ checks against a Π of the SAME grade; the domain must convert and
    -- the body checks against the codomain.
    ⇐-lam : ∀ {Γ g d b g′ d′ c}
          → g ≡ g′
          → Conversion._≈_ conv d d′
          → extend Γ d′ ⊢ b ⇐ c
          → Γ ⊢ tm-lam g d b ⇐ tm-pi g′ d′ c

    -- A hole is accepted at any goal type.
    ⇐-hole : ∀ {Γ name T} → Γ ⊢ tm-hole name ⇐ T

    -- Fallback: infer, then convert.
    ⇐-infer : ∀ {Γ t T T′}
            → Γ ⊢ t ⇒ T′
            → Conversion._≈_ conv T′ T
            → Γ ⊢ t ⇐ T

    -- Cumulative sorts: a term of type Type i checks against Type j when i ≤ j.
    ⇐-cumul : ∀ {Γ t i j}
            → Γ ⊢ t ⇒ tm-type i
            → i ≤ˡ j
            → Γ ⊢ t ⇐ tm-type j

  ------------------------------------------------------------------------
  -- Spine checking (for data params/indices and constructor args)
  ------------------------------------------------------------------------

  data _⊢*_⇐*_ where
    ⊢*[] : ∀ {Γ} → Γ ⊢* [] ⇐* []
    ⊢*∷  : ∀ {Γ x xs T tele nm}
         → Γ ⊢ x ⇐ T
         → Γ ⊢* xs ⇐* tele
         → Γ ⊢* (x ∷ xs) ⇐* ((nm , T) ∷ tele)

  ------------------------------------------------------------------------
  -- Branch checking
  --
  -- `Γ ⊢*brs brs ⇐*ᵇ (n , m)` says: for every constructor of family `n`,
  -- there is a branch whose body checks against the motive `m` applied to
  -- that constructor's result indices and value. Coverage (§3.3) requires
  -- a branch for every constructor not refuted by index unification; we
  -- model the *positive* obligation here (each present branch is
  -- well-typed) and leave the coverage side condition to Core/Coverage.agda.
  ------------------------------------------------------------------------

  data _⊢*brs_⇐*ᵇ_ where
    brs[] : ∀ {Γ n m} → Γ ⊢*brs [] ⇐*ᵇ (n , m)
    brs∷  : ∀ {Γ cn ar b brs n m f ct}
          → findCtor cn (IndEnv.families ind) ≡ just (f , ct)
          → length (ctor-args ct) ≡ ar
          → extendⁿ Γ ar ⊢ b ⇐ tm-app m (tm-ctor cn (branch-field-vars ar))
          → Γ ⊢*brs brs ⇐*ᵇ (n , m)
          → Γ ⊢*brs ((cn , ar , b) ∷ brs) ⇐*ᵇ (n , m)

