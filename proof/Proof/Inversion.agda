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
-- STATUS: legacy derivations over Conversion's reflection fields.
-- Proof.InterfaceAudit refutes those fields together with ReduceConv.
-- These are not independently established NbE injectivity theorems.
------------------------------------------------------------------------
module Proof.Inversion where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
  -- Conversion injectivity (the FSCD'25 obligation).
  --
  -- To lift the inference-mode inversion lemmas to checking mode, we need
  -- that conversion reflects the head constructor: if `T′ ≈ tm-data n ps is`
  -- then `T′` is itself a data type (with convertible arguments). This is
  -- the injectivity property, and it is provable in a meta-theory weaker
  -- than the object theory — which is why conversion soundness does not
  -- require normalisation.
  --
  -- Stated BEFORE the inversion lemmas: `invert-pi` / `invert-data` consume
  -- them in their `⇒-conv` case.
  ------------------------------------------------------------------------

  -- A type convertible to a Π IS a Π (with a convertible domain and
  -- codomain); a type convertible to a data type IS a data type (with
  -- convertible spines). Projections of the `Conversion` record's reflection
  -- fields (`Core/Typing.agda`).
  conv-injective-data :
    ∀ {T′ n ps is}
    → Conversion._≈_ conv T′ (tm-data n ps is)
    → Σ (List Term) (λ ps′ → Σ (List Term) (λ is′ → T′ ≡ tm-data n ps′ is′))
  conv-injective-data {T′} eq = Conversion.≈-data-inj conv (Conversion.≈-sym conv eq)

  conv-injective-pi :
    ∀ {T′ g d c}
    → Conversion._≈_ conv T′ (tm-pi g d c)
    → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ c′ → T′ ≡ tm-pi g′ d′ c′)))
  conv-injective-pi {T′} eq = Conversion.≈-pi-inj conv (Conversion.≈-sym conv eq)
  ------------------------------------------------------------------------
  -- Inversion of `infer` on a canonical head.
  --
  -- If `Γ ⊢ t ⇒ T` and `t` is canonical, then `T` is determined by the
  -- head of `t`. Each canonical head has exactly one applicable infer rule;
  -- the elimination rules (`⇒-app`, `⇒-case`) require the head to be a
  -- neutral, contradicting `Canonical`.
  --
  -- PROVED by induction on the inference derivation. For a canonical head,
  -- the only constructors that can apply are the corresponding introduction
  -- rule; every other rule either produces a different type shape (ruled
  -- out by the type index) or requires a non-canonical head (ruled out by
  -- `Canonical`). The `⇒-conv` case recurses via conversion injectivity.
  ------------------------------------------------------------------------
  -- A canonical value that infers a Π type is a λ.
  --
  -- This is the "app" case of Progress: the function position's type is a
  -- Π, so if the function is canonical it is a λ and β fires.
  --
  -- PROVED by induction on the inference derivation. The only rule whose
  -- conclusion type is `tm-pi g d c` is `⇒-lam` (returning the λ witness).
  -- Every other rule either yields a different type former (`⇒-type`,
  -- `⇒-pi`, `⇒-data`, the base types, `⇒-effect_*`), which Agda rules out by
  -- the type index, or has a NEUTRAL head (`⇒-var`, `⇒-global`, `⇒-app`,
  -- `⇒-let`, `⇒-case`), which `Canonical` rules out. The `⇒-conv` case is
  -- the only non-structural one: `conv-injective-pi` turns the convertible
  -- type back into a literal Π, and we recurse.
  invert-pi :
    ∀ {k} {Γ : Ctx k} {t g d c}
    → Canonical t
    → Γ ⊢ t ⇒ tm-pi g d c
    → Σ Grade (λ g′ → Σ Term (λ d′ → Σ Term (λ b → t ≡ tm-lam g′ d′ b)))
  invert-pi c-lam (⇒-lam ds body) = _ , _ , _ , refl
  invert-pi can (⇒-conv der eq) with conv-injective-pi eq
  ... | g′ , d′ , c′ , refl = invert-pi can der
  -- A canonical value that infers a data type is a CONSTRUCTOR-LIKE head.
  --
  -- This is the "case" case of Progress: the scrutinee's type is a data
  -- type, so if the scrutinee is canonical it is a constructor (or a
  -- builtin literal, which the kernel peels to a constructor via
  -- `nat_to_ctor` / `bounded_to_ctor`) and ι fires.
  --
  -- A FINDING: the naive statement "a canonical value of data type is a
  -- `tm-ctor`" is FALSE. `tm-nat_lit m` and `tm-bounded_lit k` are
  -- canonical (`c-nat_lit` / `c-bounded_lit`) and infer `tm-data Nat [] []`
  -- / `tm-data Bounded [] []` (via `⇒-nat_lit` / `⇒-bounded_lit`), but they
  -- are not `tm-ctor`s. The kernel resolves this by treating a `{:vnat, n}`
  -- as definitionally the `Z`/`S` tower (`Eval.nat_to_ctor`), so the honest
  -- canonical-form lemma is the three-way disjunction below. Progress's
  -- `case` branch consumes it by peeling the literal to a ctor.
  --
  -- PROVED by induction on the inference derivation. The conclusion type
  -- `tm-data n ps is` is produced by exactly three rules from a canonical
  -- term: `⇒-ctor` (the `tm-ctor` disjunct), `⇒-nat_lit` (the `tm-nat_lit`
  -- disjunct), and `⇒-bounded_lit` (the `tm-bounded_lit` disjunct). Every
  -- other rule yields a different type former (ruled out by the index) or
  -- has a neutral head (ruled out by `Canonical`). The `⇒-conv` case
  -- recurses after `conv-injective-data`.
  invert-data :
    ∀ {k} {Γ : Ctx k} {t n ps is}
    → Canonical t
    → Γ ⊢ t ⇒ tm-data n ps is
    → (Σ Name (λ c → Σ (List Term) (λ args → t ≡ tm-ctor c args)))
      ⊎ (Σ ℕ (λ m → t ≡ tm-nat_lit m))
      ⊎ (Σ ℕ (λ b → t ≡ tm-bounded_lit b))
  invert-data c-ctor (⇒-ctor p q) = inj₁ (_ , _ , refl)
  invert-data c-nat_lit (⇒-nat_lit p) = inj₂ (inj₁ (_ , refl))
  invert-data c-bounded_lit (⇒-bounded_lit p) = inj₂ (inj₂ (_ , refl))
  invert-data can (⇒-conv der eq) with conv-injective-data eq
  ... | ps′ , is′ , refl = invert-data can der
  -- The componentwise form of Π injectivity, used by Preservation's β case:
  -- convertible Πs have equal grades and convertible domains and codomains.
  -- A projection of the `Conversion` record's reflection field.
  conv-pi-components :
    ∀ {g d c g′ d′ c′}
    → Conversion._≈_ conv (tm-pi g′ d′ c′) (tm-pi g d c)
    → g′ ≡ g × (Conversion._≈_ conv d′ d) × (Conversion._≈_ conv c′ c)
  conv-pi-components = Conversion.≈-pi-components conv
  ------------------------------------------------------------------------
  -- Checking-mode inversion, via conversion injectivity.
  ------------------------------------------------------------------------

  invert-data-check :
    ∀ (k : ℕ) (Γ : Ctx k) {t n ps is}
    (d : Γ ⊢ t ⇐ tm-data n ps is)
    → Canonical t
    → (Σ Name (λ c → Σ (List Term) (λ args → t ≡ tm-ctor c args)))
      ⊎ (Σ ℕ (λ m → t ≡ tm-nat_lit m))
      ⊎ (Σ ℕ (λ b → t ≡ tm-bounded_lit b))
  invert-data-check _ _ (⇐-infer der eq) can
    with conv-injective-data eq
  ... | ps′ , is′ , refl = invert-data can der
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
  ... | g′ , d′ , c′ , refl = invert-pi can der
  invert-pi-check _ _ (⇐-conv der eq) can
    with conv-injective-pi eq
  ... | g′ , d′ , c′ , refl = invert-pi-check _ _ der can
  invert-pi-check _ _ ⇐-hole ()
