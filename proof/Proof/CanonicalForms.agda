------------------------------------------------------------------------
-- Canonical forms lemmas.
--
-- These are the load-bearing lemmas for Progress (docs/SOUNDNESS.md §2):
-- a well-typed CANONICAL value of a given type must have a specific head
-- shape.
--
-- A crucial subtlety the Elixir kernel's prose glosses over: a "value" in
-- the NbE sense includes NEUTRALS (stuck computations). A neutral is a
-- legitimate value of any type when it is stuck on a variable or an opaque
-- global. So the canonical-form lemma cannot say "every value of Π type is
-- a λ" — a stuck application `f a` of Π type is a value and is not a λ.
--
-- What IS true, and what Progress actually needs, is:
--
--   * a CANONICAL (non-neutral) value of Π type is a λ;
--   * a CANONICAL value of data type is a ctor.
--
-- The `Canonical`/`Neutral`/`Value` split lives in Proof/Values.agda; the
-- head-inversion lemmas the proofs consume live in Proof/Inversion.agda.
--
-- STATUS: the two lemmas are now PROVED, by composing the checking-mode
-- head-inversion lemmas of Proof/Inversion.agda. The remaining open
-- obligations are the inversion lemmas themselves (Proof/Inversion.agda)
-- and conversion injectivity.
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
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; Conversion;
                                All2; a2[]; a2∷)
open import Proof.Values using (Canonical; Neutral; Value; canonical; neutral)
open import Proof.Inversion

module CF (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv
  open Proof.Inversion.Invert ind sig conv

  -- A λ is checkable against a Π of the same grade when its body is and its
  -- domain is a well-formed type.
  lam-checks : ∀ {k} {Γ : Ctx k} {g d b c l}
             → Γ ⊢ d ⇒ tm-type l
             → extend Γ d ⊢ b ⇐ c
             → Γ ⊢ tm-lam g d b ⇐ tm-pi g d c
  lam-checks {Γ} {g} {d} {b} {c} ds body = ⇐-lam ds body

  -- A CANONICAL value of Π type is a λ.
  --
  -- PROVED: this is exactly `invert-pi-check` from Proof/Inversion.agda.
  -- Progress's `app` case consumes it: if the function position is
  -- canonical it is a λ, so β fires.
  canonical-pi-value :
    ∀ {k} {Γ : Ctx k} {g d c v}
    → Γ ⊢ v ⇐ tm-pi g d c
    → Canonical v
    → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ b → v ≡ tm-lam g′ d′ b)))
  canonical-pi-value = invert-pi-check _ _

  -- A CANONICAL value of data type is CONSTRUCTOR-LIKE: a `tm-ctor`, or a
  -- builtin `tm-nat_lit` / `tm-bounded_lit` (which the kernel peels to a
  -- ctor). The naive "is a `tm-ctor`" statement is false — see
  -- `invert-data` in Proof/Inversion.agda for the counterexample.
  --
  -- PROVED: this is exactly `invert-data-check` from Proof/Inversion.agda.
  -- Progress's `case` case consumes it: if the scrutinee is canonical it is
  -- constructor-like, so ι fires (peeling a literal to a ctor first).
  canonical-ctor :
    ∀ {k} {Γ : Ctx k} {n ps is v}
    → Γ ⊢ v ⇐ tm-data n ps is
    → Canonical v
    → (Σ Name (λ c → Σ (List Term) (λ args → v ≡ tm-ctor c args)))
      ⊎ (Σ ℕ (λ m → v ≡ tm-nat_lit m))
      ⊎ (Σ ℕ (λ b → v ≡ tm-bounded_lit b))
  canonical-ctor = invert-data-check _ _