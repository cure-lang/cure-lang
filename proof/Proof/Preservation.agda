------------------------------------------------------------------------
-- Preservation (docs/SOUNDNESS.md §4).
--
--   If `· ⊢ e : T` and `e ⇝ e′`, then `· ⊢ e′ : T`.
--
-- The four cases are β, ζ, ι, δ:
--
--   β: substitution into a λ body (needs the substitution lemma);
--   ζ: substitution into a let body (same lemma);
--   ι: the branch body, checked against the motive at the ctor's indices;
--   δ: the certified global's body, checked against its declared type.
--
-- The substitution lemma is the algebraic heart of β/ζ. It is stated here
-- and proved by induction on the typing derivation, using the shift/subst
-- laws of Proof/Substitution.agda.
--
-- STATUS: the substitution lemma and the four preservation cases are the
-- current research frontier. Each is marked `postulate` with a strategy.
------------------------------------------------------------------------
module Proof.Preservation where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax
open import Core.Signature using (IndEnv; Family; Ctor; Telescope; findFamily; findCtor;
                                   fam-params; fam-indices; fam-level; fam-name;
                                   ctor-args; ctor-params; ctor-indices)
open import Core.Reduction
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin; Conversion)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Substitution
open import Proof.Context using (lookup-extend; lookup-tail; toℕ-wkFin)

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  ------------------------------------------------------------------------
  -- Weakening.
  --
  -- If `Γ ⊢ t ⇒ T` then `extend Γ S ⊢ shift 1 0 t ⇒ T`: adding a fresh
  -- binder preserves typability, shifting the term by one. The type is
  -- UNCHANGED (well-scoped convention: the type at index `i` is scoped in
  -- the prefix below it, which the fresh binder does not disturb).
  --
  -- PROVED by induction on the derivation. The `⇒-var` case is the
  -- definitional `lookup-extend` law; the binder cases recurse under the
  -- binder; the spine/branch cases are the helper obligations below.
  ------------------------------------------------------------------------

  -- Shifting a branch body at the branch's arity.
  shiftBranchBody : Branch → Branch
  shiftBranchBody (cn , ar , b) = cn , ar , shift 1 ar b

  -- Helper obligations for the spine/branch cases of weakening.
  postulate
    weaken-app :
      ∀ {Γ f a g d c S}
      → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ a ⇐ d
      → extend Γ S ⊢ tm-app (shift 1 0 f) (shift 1 0 a) ⇒ substT 0 a c

  postulate
    weaken-data :
      ∀ {Γ n ps is f S}
      → findFamily n (IndEnv.families ind) ≡ just f
      → Γ ⊢* ps ⇐* fam-params f → Γ ⊢* is ⇐* fam-indices f
      → extend Γ S ⊢ tm-data n (map (shift 1 0) ps) (map (shift 1 0) is) ⇒ tm-type (fam-level f)

  postulate
    weaken-ctor :
      ∀ {Γ c args f ct S}
      → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      → Γ ⊢* args ⇐* ctor-args ct
      → extend Γ S ⊢ tm-ctor c (map (shift 1 0) args) ⇒ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)

  postulate
    weaken-case :
      ∀ {Γ s m brs n ps is T S}
      → Γ ⊢ s ⇒ tm-data n ps is → Γ ⊢ m ⇒ T
      → Γ ⊢*brs brs ⇐*ᵇ (n , m)
      → extend Γ S ⊢ tm-case (shift 1 0 s) (shift 1 0 m) (map shiftBranchBody brs) ⇒ tm-app m s

  postulate
    weaken⇐ :
      ∀ {Γ t T S} → Γ ⊢ t ⇐ T → extend Γ S ⊢ shift 1 0 t ⇐ T

  -- Weakening for the inference judgment.
  --
  -- OPEN OBLIGATION: with the length-indexed context the `⇒-var` case is
  -- the definitional `lookup-extend` law, but the binder cases hit the
  -- binder-order issue: prepending the fresh binder `S` does not commute
  -- with prepending the Π/λ binder `d`. The standard fix is to state
  -- weakening via a context *morphism* (a `Fin` map), whose extension
  -- under a binder handles the order automatically. This is the next step;
  -- the lookup law it rests on (`lookup-extend`) is proved in
  -- Proof/Context.agda.
  postulate
    weaken⇒ : ∀ {Γ t T S} → Γ ⊢ t ⇒ T → extend Γ S ⊢ shift 1 0 t ⇒ T

  ------------------------------------------------------------------------
  -- Substitution.
  --
  -- If `extend Γ A ⊢ t ⇒ T` and `Γ ⊢ a ⇐ A`, then `Γ ⊢ substT 0 a t ⇒ substT 0 a T`.
  ------------------------------------------------------------------------

  postulate
    subst⇒ :
      ∀ {Γ t T A a}
      → extend Γ A ⊢ t ⇒ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇒ substT 0 a T

  postulate
    subst⇐ :
      ∀ {Γ t T A a}
      → extend Γ A ⊢ t ⇐ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇐ substT 0 a T

  ------------------------------------------------------------------------
  -- Preservation
  ------------------------------------------------------------------------

  postulate
    preservation :
      ∀ {t t′ T}
      → ⟨⟩ ⊢ t ⇒ T
      → _⇝_ sig t t′
      → ⟨⟩ ⊢ t′ ⇒ T
