------------------------------------------------------------------------
-- Canonical forms lemmas.
--
-- These are the load-bearing lemmas for Progress (docs/SOUNDNESS.md §2):
-- a well-typed VALUE of a given type must have a specific head shape.
--
-- The key ones:
--   * a value of Π type is a λ (or a neutral — but a closed well-typed
--     term of Π type that is a value is a λ);
--   * a value of data type is a ctor (or a neutral).
--
-- The kernel phrases these as "the function position of a well-typed
-- application has function type, so if it is a value it is a λ". We isolate
-- them here so Progress reads cleanly.
--
-- STATUS: the statements are given; the proofs are the current research
-- frontier (see proof/README.md). Lemmas marked `postulate` are the open
-- obligations of this slice, each with a comment naming the proof strategy.
------------------------------------------------------------------------
module Proof.CanonicalForms where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade; erased; linear; affine; unrestricted)
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (Context; _∋_; here; there; extend; Conversion; All2; a2[]; a2∷)

------------------------------------------------------------------------
-- Values
--
-- The kernel's notion of a canonical form (`MetaCheck.canonical_head?/1`):
-- a value is a λ, a ctor, a Π, a Type, a data type, a literal, or an inert
-- effect former. Neutrals (stuck computations) are values too, but a
-- *closed* well-typed term that is a value is never a bare neutral at the
-- head of an elimination.
--
-- We define `Value` as the syntactic predicate that a term is in canonical
-- form. This mirrors the value domain of Core/Value.agda, but at the
-- syntactic level, which is what Progress needs.
------------------------------------------------------------------------

data Value : Term → Set where
  v-type    : ∀ {l} → Value (tm-type l)
  v-pi      : ∀ {g d c} → Value (tm-pi g d c)
  v-lam     : ∀ {g d b} → Value (tm-lam g d b)
  v-data    : ∀ {n ps is} → Value (tm-data n ps is)
  v-ctor    : ∀ {n args} → Value (tm-ctor n args)
  v-int_type    : Value tm-int_type
  v-int_lit     : ∀ {k} → Value (tm-int_lit k)
  v-nat_lit     : ∀ {k} → Value (tm-nat_lit k)
  v-bounded_lit : ∀ {k} → Value (tm-bounded_lit k)
  v-float_type  : Value tm-float_type
  v-float_lit   : Value tm-float_lit
  v-binary_type : Value tm-binary_type
  v-atom_type   : Value tm-atom_type
  v-atom_lit    : ∀ {n} → Value (tm-atom_lit n)
  v-effect_type : ∀ {t} → Value (tm-effect_type t)
  v-effect_pure : ∀ {t} → Value (tm-effect_pure t)
  v-effect_bind : ∀ {e k} → Value (tm-effect_bind e k)
  -- A neutral (stuck) term is a value: a variable, a global, a hole, or an
  -- application/case whose head is stuck.
  v-var    : ∀ {k} → Value (tm-var k)
  v-global : ∀ {n} → Value (tm-global n)
  v-hole   : ∀ {n} → Value (tm-hole n)
  v-app-stuck : ∀ {f a} → Value f → Value (tm-app f a)
  v-case-stuck : ∀ {s m brs} → Value s → Value (tm-case s m brs)

------------------------------------------------------------------------
-- Canonical forms: a value of a given type has a specific head shape.
--
-- Stated over the typing judgment `Typing ind sig conv`.
------------------------------------------------------------------------

module CF (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  -- A λ is checkable against a Π of the same grade when its body is.
  --
  -- This is the `⇐-lam` rule packaged as a lemma, used by Progress's
  -- application case: a value of Π type that is a λ β-reduces.
  lam-checks : ∀ {Γ g d b c}
             → extend Γ d ⊢ b ⇐ c
             → Γ ⊢ tm-lam g d b ⇐ tm-pi g d c
  lam-checks {Γ} {g} {d} {b} {c} body = ⇐-lam refl (Conversion.≈-refl conv) body

  -- A CLOSED value of Π type is a λ.
  --
  -- Proof strategy: by cases on the typing derivation. The only infer rule
  -- that yields `tm-pi` from a canonical value is `⇒-lam` (a λ — done).
  -- `⇒-global`/`⇒-app`/`⇒-case` produce a neutral head, which for a CLOSED
  -- term is impossible (a closed neutral has an unbound variable, an opaque
  -- global, or a stuck eliminator — none of which is a closed canonical
  -- value of Π type). Checking-mode rules (`⇐-lam`, `⇐-infer`, `⇐-cumul`)
  -- either give a λ or reduce to inference.
  --
  -- OPEN OBLIGATION: the value-level statement. This is what Progress's
  -- `app` case consumes: if the function position is a value of Π type, it
  -- is a λ, so β fires.
  postulate
    canonical-pi-value :
      ∀ {Γ g d c v}
      → Γ ⊢ v ⇐ tm-pi g d c
      → Value v
      → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ b → v ≡ tm-lam g′ d′ b)))

  -- A CLOSED value of data type is a ctor.
  --
  -- Proof strategy: the only infer rule yielding `tm-data` from a value is
  -- `⇒-ctor`; `⇒-data` yields a *sort*, not a data *value*; the elimination
  -- rules produce neutrals. This is the lemma that makes ι fire in Progress.
  --
  -- OPEN OBLIGATION: the value-level statement.
  postulate
    canonical-ctor :
      ∀ {Γ n ps is v}
      → Γ ⊢ v ⇐ tm-data n ps is
      → Value v
      → Σ Name (λ c → Σ (List Term) (λ args → v ≡ tm-ctor c args))
