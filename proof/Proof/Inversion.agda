------------------------------------------------------------------------
-- Head inversion lemmas.
--
-- The canonical-form lemmas (Proof/CanonicalForms.agda) need to invert an
-- inference derivation on a canonical head: if `Γ ⊢ c args ⇒ T` and the
-- head `c` is a canonical introduction form, then `T` has a specific shape.
--
-- These are the standard "inversion of typing" lemmas. They are stated
-- here, separately from the canonical-form lemmas, because they are the
-- reusable core: Progress, Preservation, and the canonical-form lemmas all
-- consume them.
--
-- A NOTE ON CONVERSION. The checking-mode lemmas (`⇐-infer` composes an
-- inference with a conversion test) cannot be inverted without knowing
-- that conversion is INJECTIVE on type constructors: `T′ ≈ tm-data n ps is`
-- does not syntactically determine `T′`. That injectivity is exactly the
-- property Lennon-Bertrand's *What does it take to certify a conversion
-- checker?* (FSCD'25) isolates as the sole requirement for conversion
-- soundness. We therefore state the inversion lemmas over INFERENCE
-- derivations, where the type is syntactically determined, and record the
-- conversion-injectivity obligation separately.
--
-- STATUS: statements given; proofs are the current research frontier. Each
-- is marked `postulate` with a named strategy.
------------------------------------------------------------------------
module Proof.Inversion where

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

module Invert (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  ------------------------------------------------------------------------
  -- Inversion of `infer` on a canonical head.
  --
  -- If `Γ ⊢ t ⇒ T` and `t` is canonical, then `T` is determined by the
  -- head of `t`. Each canonical head has exactly one applicable infer rule;
  -- the elimination rules (`⇒-app`, `⇒-case`) require the head to be a
  -- neutral, contradicting `Canonical`.
  --
  -- Proof strategy: induction on the inference derivation. For a canonical
  -- head, the only constructors that can apply are the corresponding
  -- introduction rule; every other rule either produces a different type
  -- shape or requires a non-canonical head.
  ------------------------------------------------------------------------

  -- A canonical value that infers a Π type is a λ.
  --
  -- This is the "app" case of Progress: the function position's type is a
  -- Π, so if the function is canonical it is a λ and β fires.
  --
  -- Proof sketch: the only inference rule whose conclusion type is
  -- `tm-pi g d c` is `⇒-lam` (which yields `tm-pi g d T` for the inferred
  -- body type `T`), so `c ≡ T` and the term is `tm-lam g d b`. Every other
  -- rule yields a `tm-type`, `tm-data`, or a base type, or requires a
  -- neutral head.
  postulate
    invert-pi :
      ∀ {k} {Γ : Ctx k} {t g d c}
      → Γ ⊢ t ⇒ tm-pi g d c
      → Canonical t
      → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ b → t ≡ tm-lam g′ d′ b)))

  -- A canonical value that infers a data type is a ctor.
  --
  -- This is the "case" case of Progress: the scrutinee's type is a data
  -- type, so if the scrutinee is canonical it is a ctor and ι fires.
  --
  -- Proof sketch: the only inference rule whose conclusion type is
  -- `tm-data n ps is` from a canonical value is `⇒-ctor`. `⇒-data` yields
  -- `tm-type (fam-level f)`, not a data value; the elimination rules
  -- require a neutral head.
  postulate
    invert-data :
      ∀ {k} {Γ : Ctx k} {t n ps is}
      → Γ ⊢ t ⇒ tm-data n ps is
      → Canonical t
      → Σ Name (λ c → Σ (List Term) (λ args → t ≡ tm-ctor c args))

  ------------------------------------------------------------------------
  -- Conversion injectivity (the FSCD'25 obligation).
  --
  -- To lift the inference-mode inversion lemmas to checking mode, we need
  -- that conversion reflects the head constructor: if `T′ ≈ tm-data n ps is`
  -- then `T′` is itself a data type (with convertible arguments). This is
  -- the injectivity property, and it is provable in a meta-theory weaker
  -- than the object theory — which is why conversion soundness does not
  -- require normalisation.
  ------------------------------------------------------------------------

  -- Conversion injectivity on the type constructors: a type convertible to
  -- a Π IS a Π (with a convertible domain and codomain); a type convertible
  -- to a data type IS a data type (with convertible spines). This is the
  -- FSCD'25 property, stated in the form the inversion and β lemmas consume.
  postulate
    conv-injective-data :
      ∀ {T′ n ps is}
      → Conversion._≈_ conv T′ (tm-data n ps is)
      → Σ (List Term) (λ ps′ → Σ (List Term) (λ is′ → T′ ≡ tm-data n ps′ is′))

  postulate
    conv-injective-pi :
      ∀ {T′ g d c}
      → Conversion._≈_ conv T′ (tm-pi g d c)
      → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ c′ → T′ ≡ tm-pi g′ d′ c′)))

  -- The componentwise form of Π injectivity, used by Preservation's β case:
  -- convertible Πs have equal grades and convertible domains and codomains.
  postulate
    conv-pi-components :
      ∀ {g d c g′ d′ c′}
      → Conversion._≈_ conv (tm-pi g′ d′ c′) (tm-pi g d c)
      → g′ ≡ g × (Conversion._≈_ conv d′ d) × (Conversion._≈_ conv c′ c)

  ------------------------------------------------------------------------
  -- Checking-mode inversion, via conversion injectivity.
  ------------------------------------------------------------------------

  invert-data-check :
    ∀ (k : ℕ) (Γ : Ctx k) {t n ps is}
    (d : Γ ⊢ t ⇐ tm-data n ps is)
    → Canonical t
    → Σ Name (λ c → Σ (List Term) (λ args → t ≡ tm-ctor c args))
  invert-data-check _ _ (⇐-infer der eq) can
    with conv-injective-data eq
  ... | ps′ , is′ , refl = invert-data der can
  invert-data-check _ _ (⇐-conv der eq) can
    with conv-injective-data eq
  ... | ps′ , is′ , refl = invert-data-check _ _ der can
  invert-data-check _ _ ⇐-hole ()

  invert-pi-check :
    ∀ (k : ℕ) (Γ : Ctx k) {t g d c}
    (d : Γ ⊢ t ⇐ tm-pi g d c)
    → Canonical t
    → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ b → t ≡ tm-lam g′ d′ b)))
  invert-pi-check _ _ (⇐-lam ds x) can = _ , _ , _ , refl
  invert-pi-check _ _ (⇐-infer der eq) can
    with conv-injective-pi eq
  ... | g′ , d′ , c′ , refl = invert-pi der can
  invert-pi-check _ _ (⇐-conv der eq) can
    with conv-injective-pi eq
  ... | g′ , d′ , c′ , refl = invert-pi-check _ _ der can
  invert-pi-check _ _ ⇐-hole ()
