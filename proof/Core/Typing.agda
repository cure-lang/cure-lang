------------------------------------------------------------------------
-- Declarative typing built from bidirectional introduction/elimination.
--
-- The executable `Cure.Core.Kernel` (lib/cure/core/kernel.ex) provides:
--
--   infer(Γ, e) = {:ok, T}   — synthesise the type T
--   check(Γ, e, T) = :ok     — verify e against the expected type T,
--                              falling back to infer plus a cumulative
--                              conversion test (`check_via_infer`).
--
-- Here `Γ ⊢ e ⇒ T` is CLOSED under conversion and cumulative sorts; it is
-- NOT the graph of executable minimal type synthesis. `Γ ⊢ e ⇐ T` is the
-- checking judgment. Contexts are telescopes; types are raw Terms.
--
-- Types are compared by an abstract Conversion record, not an established
-- implementation of NbE. Cumulativity is separate from equality:
-- `Type i <: Type j` when `i ≤ j`.
--
-- The context is a list of types, most-recent first (de Bruijn index 0 at
-- the head), matching `Cure.Core.Context`.
------------------------------------------------------------------------
module Core.Typing where

open import Data.Bool using (Bool; true; false)
open import Data.String using (_==_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_; _≤ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; _++_; length; map; reverse)
open import Data.List using () renaming (lookup to listLookup)
open import Data.List.Properties using (length-reverse)
open import Data.Fin using (Fin; zero; suc; toℕ; _↑ˡ_)
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
open import Core.TypeHeads
open import Core.Signature
open import Core.Coverage using (CaseCoverage)
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

-- A context is a LENGTH-INDEXED telescope of types, most-recent first.
-- Putting the length in the type makes `extend` definitional
-- (`extend : Ctx n → Term → Ctx (suc n)`), which removes every `Fin`
-- transport from the weakening and substitution lemmas.
--
-- The context stores types in the GLOBAL de Bruijn convention: prepending a
-- binder renames every existing type by `wk` (`wk k = suc k`), so a stored
-- type's free variables keep referring to the same binders.
data Ctx : ℕ → Set where
  ⟨⟩  : Ctx zero
  _▷_ : ∀ {n} → Ctx n → Term → Ctx (suc n)

-- Variable lookup: a `Fin n` into a `Ctx n` gives the type of that variable.
-- Index 0 is the most-recently-bound variable (the head). This is a total
-- function, mirroring the kernel's `Context.lookup(ctx, k)`.
lookup : ∀ {n} → Ctx n → Fin n → Term
lookup (Γ ▷ T) zero = T
lookup (Γ ▷ T) (suc i) = lookup Γ i

-- Rename every type in a context.
renameCtx : Ren → ∀ {n} → Ctx n → Ctx n
renameCtx ρ ⟨⟩ = ⟨⟩
renameCtx ρ (Γ ▷ T) = renameCtx ρ Γ ▷ rename ρ T

-- Context extension: prepend a fresh binder, renaming every existing type
-- by `wk` (the global de Bruijn convention). Definitional length.
extend : ∀ {n} → Ctx n → Term → Ctx (suc n)
extend Γ T = renameCtx wk Γ ▷ rename wk T

-- Looking up a renamed context.
lookup-renameCtx : ∀ {n} (ρ : Ren) (Γ : Ctx n) (i : Fin n)
                 → lookup (renameCtx ρ Γ) i ≡ rename ρ (lookup Γ i)
lookup-renameCtx ρ (Γ ▷ T) zero = refl
lookup-renameCtx ρ (Γ ▷ T) (suc i) = lookup-renameCtx ρ Γ i

-- The weakening lookup law: after extending, an existing variable is found
-- at the lifted index, with its type renamed by `wk`.
lookup-extend : ∀ {n} (Γ : Ctx n) (T : Term) (i : Fin n)
              → lookup (extend Γ T) (suc i) ≡ rename wk (lookup Γ i)
lookup-extend Γ T i = lookup-renameCtx wk Γ i

------------------------------------------------------------------------
-- Conversion (definitional equality)
--
-- We take `_≈_` as a parameter of the typing judgment — it is the
-- proposed syntactic counterpart of the kernel's NbE conversion. Here we
-- specify the laws consumed by the conditional typing proofs.
--
-- Making it a record (rather than a bare relation) keeps the soundness
-- theorem honest about what it assumes: conversion is an equivalence that
-- is a congruence for the type formers the kernel's `Conv` implements.
--
-- SCOPE — η IS NOT MODELLED HERE (docs/SOUNDNESS.md §8.5).
--
-- The kernel's conversion DOES perform η: `Conv.conv_struct?/4`
-- (`lib/cure/core/conv.ex`) compares a `vlam` against a NON-`vlam` by
-- applying both to a fresh neutral (`eta_eq?/4`), and compares `vlam`
-- against `vlam` by grade equality plus the same η test. This record has no
-- η field — there is no `≈-lam` congruence and no "λ x. f x ≈ f" rule.
--
-- Raw syntax-head reflection has been removed; the historical impossible
-- property is frozen only in Proof.InterfaceAudit. Rigid head separation
-- applies only to two exposed type formers, preserving exact universe
-- levels and family names. Cumulative sorts belong to typing, not ≈.
--
-- Proof.ReductionConversion inhabits this record together with FULL
-- ReduceConv, via common reducts after literal expansion and checked
-- confluence. Proof.SoundnessModel jointly instantiates the current
-- closed-entry soundness hypotheses on a nonempty fragment.
-- APPLICABILITY WARNING: this model omits eta (a negative control proves
-- that omission). Exact-arity closed-entry branch order now agrees with
-- the executable frame; NbE refinement, dependent signatures, parameter
-- filtering and missing erased slots remain open.
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
    -- STABILITY UNDER RENAMING AND SUBSTITUTION.
    --
    -- Required laws, not consequences of structurally deciding equality.
    -- Their implementation refinement remains to be proved. These fields
    -- are exactly the `rename-conv` /
    -- `subst-conv` obligations of the renaming and substitution lemmas
    -- (Proof/Preservation.agda), which become projections.
    ≈-rename   : ∀ {t u} (ρ : Ren) → t ≈ u → rename ρ t ≈ rename ρ u
    ≈-subst    : ∀ {t u} (σ : Sub) → t ≈ u → substS σ t ≈ substS σ u
    -- Substitution congruence: pointwise-convertible substitutions give
    -- convertible results. This is what lets `ξ-app₂` / `ξ-let` / `ξ-case`
    -- relate `substTopT a c` to `substTopT a′ c` when the argument steps.
    ≈-subst-cong : ∀ {t} {σ σ′ : Sub} → (∀ i → σ i ≈ σ′ i) → substS σ t ≈ substS σ′ t
    -- RIGID HEAD SEPARATION AND PI COMPONENT INJECTIVITY.
    -- Separation is required only for TWO rigid type formers. It never
    -- concludes that an arbitrary converted term is literally a Pi/data.
    ≈-heads : ∀ {t u h h′}
      → HasTypeHead t h → HasTypeHead u h′ → t ≈ u → h ≡ h′
    ≈-pi-components : ∀ {g d c g′ d′ c′}
                    → tm-pi g′ d′ c′ ≈ tm-pi g d c
                    → g′ ≡ g × (d′ ≈ d) × (c′ ≈ c)
    -- THE COMPACT-LITERAL IDENTIFICATION.
    --
    -- The kernel treats a compact `{:vnat, n}` as the `Z`/`S` tower
    -- (`Eval.nat_to_ctor`; `bounded_to_ctor` for bounded), so a `case` on a
    -- literal fires ι after PEELING the literal to a constructor. These
    -- fields record that identification: a compact literal is
    -- definitionally equal to the constructor term it peels to. This is
    -- what makes the literal-peel ι rules (`ι-nat-*` / `ι-bounded-*`)
    -- type-preserving.
    ≈-nat-zero  : tm-ctor "Z" [] ≈ tm-nat_lit 0
    ≈-nat-suc   : ∀ {k} → tm-ctor "S" (tm-nat_lit k ∷ []) ≈ tm-nat_lit (suc k)
    ≈-bounded-zero : tm-ctor "First" (tm-nat_lit 0 ∷ []) ≈ tm-bounded_lit 0
    ≈-bounded-suc  : ∀ {k} → tm-ctor "Next" (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) ≈ tm-bounded_lit (suc k)
open Conversion public

------------------------------------------------------------------------
-- The multi-binder context extension.
--
-- `extendⁿ Γ k` prepends `k` fresh `tm-hole "field"` binders (the branch
-- fields of a `case`). It is defined at the top level (it depends only on
-- `Ctx`/`extend`, not on the typing judgment), so the context lemmas in
-- Proof/Context.agda can import it directly.
--
-- The result is indexed by `k + m` (NOT `m + k`): with `_+_` recursing on
-- its FIRST argument, `suc k + m ≡ suc (k + m)` and `zero + m ≡ m` hold
-- definitionally, so this recursion is CAST-FREE. That is what makes the
-- branch lookup laws `refl`-level, matching the rest of the context design.
------------------------------------------------------------------------

extendⁿ : ∀ {m} → Ctx m → (k : ℕ) → Ctx (k + m)
extendⁿ Γ zero = Γ
extendⁿ Γ (suc k) = extend (extendⁿ Γ k) (tm-hole "field")

------------------------------------------------------------------------
-- Extending a context by a TELESCOPE.
--
-- `extendTele Γ [(nm₁ , A₁) , … , (nm_ar , A_ar)]` binds the telescope's
-- entries, the FIRST entry INNERMOST:
--
--     Γ ▷ A_ar ▷ … ▷ A₁
--
-- so `A₁` is at index 0 and `A_i` at index `i - 1`. This matches
-- `branch-field-vars ar = [0, …, ar-1]`: field `i` (1-indexed) is the
-- variable at index `i - 1`.
--
-- This is an environment-order algebraic helper, NOT the surface-order
-- branch context. The active case rule uses branch-context, applying
-- extendTele to the REVERSED closed-entry constructor telescope.
--
-- Indexed by `length tele + m` and CAST-FREE (like `extendⁿ`).
------------------------------------------------------------------------

extendTele : ∀ {m} (Γ : Ctx m) (tele : Telescope) → Ctx (length tele + m)
extendTele Γ [] = Γ
extendTele Γ ((nm , T) ∷ tele) = extend (extendTele Γ tele) T

-- The type bound at de Bruijn index `i` by `extendTele Γ tele`, for a FIELD
-- position (`i < length tele`): the `i`-th telescope entry (0-indexed).
teleField : (tele : Telescope) → Fin (length tele) → Term
teleField tele i = proj₂ (listLookup tele i)

-- The field index `i` as an index into `extendTele Γ tele`.
fieldFin : ∀ {m} (tele : Telescope) → Fin (length tele) → Fin (length tele + m)
fieldFin tele i = i ↑ˡ _

------------------------------------------------------------------------
-- Ascending environment-slot variables, used as an algebraic helper.
-- Active branches reconstruct a constructor using surface-field-vars
-- [ar-1, …, 0], since the LAST declared field is innermost.
------------------------------------------------------------------------

upto : ℕ → List ℕ
upto zero = []
upto (suc n) = 0 ∷ map suc (upto n)

branch-field-vars : ℕ → List Term
branch-field-vars ar = map tm-var (upto ar)

-- Closed-entry runtime branch frame: the last declared field is innermost.
-- The reversed length is used definitionally to avoid context-index casts;
-- length-reverse proves it is the declaration's ordinary arity.
branch-arity : Telescope → ℕ
branch-arity tele = length (reverse tele)

branch-context : ∀ {n} (Γ : Ctx n) (tele : Telescope) → Ctx (branch-arity tele + n)
branch-context Γ tele = extendTele Γ (reverse tele)

surface-field-vars : ℕ → List Term
surface-field-vars ar = reverse (branch-field-vars ar)

------------------------------------------------------------------------
-- Telescope membership and maps.
--
-- Purely syntactic, so they live at the TOP LEVEL (outside `module Typing`):
-- the explicit closed-entry fragment invariant
-- (`Core.ClosedFragment.ClosedFragmentSig`) consumes `_∈Tele_`.
------------------------------------------------------------------------

-- Telescope membership.
data _∈Tele_ : Term → Telescope → Set where
  ∈-here  : ∀ {T tele nm} → T ∈Tele ((nm , T) ∷ tele)
  ∈-there : ∀ {T U tele nm} → T ∈Tele tele → T ∈Tele ((nm , U) ∷ tele)

-- The `j`-th telescope entry is a member of the telescope.
listLookup-∈Tele : ∀ (tele : Telescope) (j : Fin (length tele))
                 → proj₂ (listLookup tele j) ∈Tele tele
listLookup-∈Tele (x ∷ tele) zero = ∈-here
listLookup-∈Tele (x ∷ tele) (suc j) = ∈-there (listLookup-∈Tele tele j)

-- Rename every type in a telescope.
renameTele : Ren → Telescope → Telescope
renameTele ρ [] = []
renameTele ρ ((nm , T) ∷ tele) = (nm , rename ρ T) ∷ renameTele ρ tele

-- Substitute into every type in a telescope.
substTele : Sub → Telescope → Telescope
substTele σ [] = []
substTele σ ((nm , T) ∷ tele) = (nm , substS σ T) ∷ substTele σ tele

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
  data _⊢_⇒_ : ∀ {n} → Ctx n → Term → Term → Set
  data _⊢_⇐_ : ∀ {n} → Ctx n → Term → Term → Set

  -- Flat spine checking: declarations are not instantiated at preceding
  -- arguments. Dependent checking lives in Proof.DependentSpine.
  data _⊢*_⇐*_ : ∀ {n} → Ctx n → List Term → Telescope → Set

  -- Branch checking: a list of branches against a family and its motive.
  data _⊢*brs_⇐*ᵇ_ : ∀ {n} → Ctx n → List Branch → (Name × Term) → Set

  ------------------------------------------------------------------------
  -- Helpers
  ------------------------------------------------------------------------

  -- Substituting a value at the top of a type (for the `let` rule). This is
  -- `substTopT` from Core.Syntax, re-exported inside the typing module.
  substTopT-unfold : ∀ v T → substTopT v T ≡ substS (topSub v) T
  substTopT-unfold v T = refl

  data _⊢_⇒_ where

    -- Type l : Type (l+1), when the successor is in range.
    ⇒-type : ∀ {n} {Γ : Ctx n} {l l′} → succLevel l ≡ just l′
           → Γ ⊢ tm-type l ⇒ tm-type l′

    -- Variables: the type is the context's entry at the variable's index.
    ⇒-var : ∀ {n} {Γ : Ctx n} (i : Fin n)
          → Γ ⊢ tm-var (toℕ i) ⇒ lookup Γ i

    -- Π formation: dom : Type l1, cod : Type l2 under the binder, so
    -- Π lives at max(l1, l2).
    ⇒-pi : ∀ {n} {Γ : Ctx n} {g d c l1 l2}
         → Γ ⊢ d ⇒ tm-type l1
         → extend Γ d ⊢ c ⇒ tm-type l2
         → Γ ⊢ tm-pi g d c ⇒ tm-type (l1 ⊔ˡ l2)

    -- λ inference: infer the domain's sort, CHECK the body against the
    -- codomain, and form the Π type. Checking (rather than inferring) the
    -- body is what lets `value-infer` turn a checked λ into an inferring
    -- one, which Preservation's β/ζ cases need.
    ⇒-lam : ∀ {n} {Γ : Ctx n} {g d b l c}
          → Γ ⊢ d ⇒ tm-type l
          → extend Γ d ⊢ b ⇐ c
          → Γ ⊢ tm-lam g d b ⇒ tm-pi g d c

    -- Application: infer the function type, require it to be a Π, INFER
    -- the argument's type (which must convert to the domain), and return the
    -- codomain instantiated at the argument.
    --
    -- The instantiation is the TOP substitution `substTopT a c = substS
    -- (topSub a) c` — the simultaneous-substitution presentation used
    -- throughout. This matches the kernel's
    -- `Eval.apply_closure(cod_closure, a_value)`, which evaluates the
    -- codomain in the environment `[a_value | env]` — i.e. it PREPENDS the
    -- argument (index 0) and shifts everything else.
    --
    -- The argument is INFERRED (not checked): the substitution lemma's head
    -- case needs the argument to infer its type, and a checked argument does
    -- not in general infer it (a λ checked via `⇐-lam` need not have an
    -- inferable domain). The kernel's `check_via_infer` infers the argument
    -- internally, so inferring it here is faithful.
    ⇒-app : ∀ {n} {Γ : Ctx n} {f a g d c}
          → Γ ⊢ f ⇒ tm-pi g d c
          → Γ ⊢ a ⇒ d
          → Γ ⊢ tm-app f a ⇒ substTopT a c

    -- let (ζ-transparent): check the value against the ascription, then
    -- infer the body under a context extended with the value's type. The
    -- result type substitutes the value for the bound variable, mirroring
    -- the kernel's `Context.extend_def` (the variable is definitionally its
    -- value), so the reported type lives in `Γ`.
    ⇒-let : ∀ {n} {Γ : Ctx n} {g ty v b l T}
          → Γ ⊢ ty ⇒ tm-type l
          → Γ ⊢ v ⇐ ty
          → extend Γ ty ⊢ b ⇒ T
          → Γ ⊢ tm-let g ty v b ⇒ substTopT v T

    -- Global: look up the declared type in the signature.
    ⇒-global : ∀ {n} {Γ : Ctx n} {f T} → Signature.type-of sig f ≡ just T → Γ ⊢ tm-global f ⇒ T

    -- Primitive base types live in Type 0.
    ⇒-int_type    : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-int_type ⇒ tm-type l0
    ⇒-float_type  : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-float_type ⇒ tm-type l0
    ⇒-binary_type : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-binary_type ⇒ tm-type l0
    ⇒-atom_type   : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-atom_type ⇒ tm-type l0

    -- Literals inhabit their base types.
    ⇒-int_lit   : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ tm-int_lit k ⇒ tm-int_type
    ⇒-float_lit : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-float_lit ⇒ tm-float_type
    ⇒-atom_lit  : ∀ {n} {Γ : Ctx n} {m} → Γ ⊢ tm-atom_lit m ⇒ tm-atom_type

    -- Nat/Bounded literals inhabit their (builtin) families.
    ⇒-nat_lit     : ∀ {n} {Γ : Ctx n} {m N} → IndEnv.builtins ind "nat" ≡ just N → Γ ⊢ tm-nat_lit m ⇒ tm-data N [] []
    ⇒-bounded_lit : ∀ {n} {Γ : Ctx n} {k B} → IndEnv.builtins ind "bounded" ≡ just B → Γ ⊢ tm-bounded_lit k ⇒ tm-data B [] []

    -- Data formation: check the params and indices against the family's
    -- telescopes; the family lives at its declared level.
    ⇒-data : ∀ {n} {Γ : Ctx n} {n ps is f}
           → findFamily n (IndEnv.families ind) ≡ just f
           → Γ ⊢* ps ⇐* fam-params f
           → Γ ⊢* is ⇐* fam-indices f
           → Γ ⊢ tm-data n ps is ⇒ tm-type (fam-level f)

    -- Constructor: check the args against the constructor's telescope and
    -- compute the result data type.
    ⇒-ctor : ∀ {n} {Γ : Ctx n} {c args f ct}
           → findCtor c (IndEnv.families ind) ≡ just (f , ct)
           → Γ ⊢* args ⇐* ctor-args ct
           → Γ ⊢ tm-ctor c args ⇒ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)

    -- Dependent case: the scrutinee's type must be a data type; the motive
    -- must be a type family; every possible branch must be present and
    -- type-check against the motive instantiated at its constructor.
    --
    -- The result type is the motive applied to the scrutinee
    -- (`apply_motive` in the kernel).
    ⇒-case : ∀ {n} {Γ : Ctx n} {s m brs n ps is T}
           → Γ ⊢ s ⇒ tm-data n ps is
           → Γ ⊢ m ⇒ T
           → Γ ⊢*brs brs ⇐*ᵇ (n , m)
           → CaseCoverage ind n brs
           → Γ ⊢ tm-case s m brs ⇒ tm-app m s

    -- Inert effects: Effect(t) is level-preserving.
    ⇒-effect_type : ∀ {n} {Γ : Ctx n} {t l} → Γ ⊢ t ⇒ tm-type l → Γ ⊢ tm-effect_type t ⇒ tm-type l
    ⇒-effect_pure : ∀ {n} {Γ : Ctx n} {a A} → Γ ⊢ a ⇒ A → Γ ⊢ tm-effect_pure a ⇒ tm-effect_type A
    ⇒-effect_bind : ∀ {n} {Γ : Ctx n} {e k A B}
                  → Γ ⊢ e ⇒ tm-effect_type A
                  → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type (rename wk B))
                  → Γ ⊢ tm-effect_bind e k ⇒ tm-effect_type B

    -- Conversion on the inferred type. This is the syntactic closure of
    -- inference under conversion; it is what lets a CHECKED value be
    -- treated as an INFERRING one (`value-infer`), which Preservation's
    -- ζ case needs.
    ⇒-conv : ∀ {n} {Γ : Ctx n} {t T T′}
           → Γ ⊢ t ⇒ T
           → Conversion._≈_ conv T T′
           → Γ ⊢ t ⇒ T′

    -- Declarative closure of synthesis under cumulative sorts. This does
    -- not identify universe levels by symmetric conversion and does NOT
    -- claim the executable inference algorithm returns the larger sort.
    ⇒-cumul : ∀ {n} {Γ : Ctx n} {t i j}
            → Γ ⊢ t ⇒ tm-type i → i ≤ˡ j → Γ ⊢ t ⇒ tm-type j

    -- A hole has no inference rule (it is checkable at any type).
    -- {:absurd} is rejected in reachable position (no inference rule).

  -- Checking judgment.
  data _⊢_⇐_ where

    -- A λ checks against a Π of the SAME grade; the domain must convert and
    -- the body checks against the codomain.
    ⇐-lam : ∀ {n} {Γ : Ctx n} {g d b c l}
          → Γ ⊢ d ⇒ tm-type l
          → extend Γ d ⊢ b ⇐ c
          → Γ ⊢ tm-lam g d b ⇐ tm-pi g d c

    -- A hole is accepted at any goal type.
    ⇐-hole : ∀ {n} {Γ : Ctx n} {name T} → Γ ⊢ tm-hole name ⇐ T

    -- Fallback: infer, then convert.
    ⇐-infer : ∀ {n} {Γ : Ctx n} {t T T′}
            → Γ ⊢ t ⇒ T′
            → Conversion._≈_ conv T′ T
            → Γ ⊢ t ⇐ T

    -- Conversion on the checked type: if `t` checks against `T` and `T ≈ T′`,
    -- then `t` checks against `T′`. (Checking is closed under conversion of
    -- the goal type.)
    ⇐-conv : ∀ {n} {Γ : Ctx n} {t T T′}
           → Γ ⊢ t ⇐ T
           → Conversion._≈_ conv T T′
           → Γ ⊢ t ⇐ T′

    -- Cumulative sorts: a term of type Type i checks against Type j when i ≤ j.
    ⇐-cumul : ∀ {n} {Γ : Ctx n} {t i j}
            → Γ ⊢ t ⇒ tm-type i
            → i ≤ˡ j
            → Γ ⊢ t ⇐ tm-type j

  ------------------------------------------------------------------------
  -- Spine checking (for data params/indices and constructor args)
  ------------------------------------------------------------------------

  data _⊢*_⇐*_ where
    ⊢*[] : ∀ {n} {Γ : Ctx n} → Γ ⊢* [] ⇐* []
    ⊢*∷  : ∀ {n} {Γ : Ctx n} {x xs T tele nm}
         → Γ ⊢ x ⇐ T
         → Γ ⊢* xs ⇐* tele
         → Γ ⊢* (x ∷ xs) ⇐* ((nm , T) ∷ tele)

  -- A checked spine has the same length as its telescope. Used by Progress's
  -- `case`/ι case to discharge the `length args ≡ ar` premise of the ι rule:
  -- `⇒-ctor` checks the constructor args against `ctor-args ct`, and the
  -- branch's `brs∷` fixes `ar = branch-arity (ctor-args ct)`,
  -- equal to length (ctor-args ct) by length-reverse.
  spine-length : ∀ {n} {Γ : Ctx n} {ts tele}
               → Γ ⊢* ts ⇐* tele → length ts ≡ length tele
  spine-length ⊢*[] = refl
  spine-length (⊢*∷ _ dxs) = cong suc (spine-length dxs)
  ------------------------------------------------------------------------
  -- Branch checking
  --
  -- `Γ ⊢*brs brs ⇐*ᵇ (n , m)` says: for every constructor of family `n`,
  -- there is a branch whose body checks against the motive `m` applied to
  -- that constructor's result indices and value. Coverage (§3.3) requires
  -- a branch for every constructor not refuted by index unification; we
  -- model the *positive* obligation here (each present branch is
  -- well-typed). The ⇒-case rule separately requires local CaseCoverage;
  -- an empty list of checked branches alone does not admit an inhabited case.
  ------------------------------------------------------------------------

  data _⊢*brs_⇐*ᵇ_ where
    brs[] : ∀ {k} {Γ : Ctx k} {n m} → Γ ⊢*brs [] ⇐*ᵇ (n , m)
    brs∷  : ∀ {k} {Γ : Ctx k} {cn b brs n m f ct}
          → findCtor cn (IndEnv.families ind) ≡ just (f , ct)
          → branch-context Γ (ctor-args ct)
              ⊢ b ⇐ tm-app (rename (λ j → j + branch-arity (ctor-args ct)) m)
                           (tm-ctor cn (surface-field-vars (branch-arity (ctor-args ct))))
          → Γ ⊢*brs brs ⇐*ᵇ (n , m)
          → Γ ⊢*brs ((cn , branch-arity (ctor-args ct) , b) ∷ brs) ⇐*ᵇ (n , m)

