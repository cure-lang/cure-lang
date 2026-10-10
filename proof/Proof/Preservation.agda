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
-- with the well-formedness condition on the context that makes the
-- `⇒-var` cases go through, and proved by induction on the derivation.
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
open import Data.Unit using (⊤; tt)
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
open import Proof.Context using (lookup-weaken; lookup-head; toℕ-wkFin)

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  ------------------------------------------------------------------------
  -- Well-formedness of a context.
  --
  -- The type at index `k` is scoped in the prefix below it. This is the
  -- standard well-formed-context condition, and it is exactly what makes
  -- the `⇒-var` cases of the substitution lemma go through: substituting a
  -- variable leaves the types of the OTHER variables unchanged.
  ------------------------------------------------------------------------

  WfCtx : Context → Set
  WfCtx ⟨⟩ = ⊤
  WfCtx (Γ ▷ T) = WfCtx Γ × Scoped (lengthCtx Γ) T

  ------------------------------------------------------------------------
  -- Weakening.
  --
  -- If `Γ ⊢ t ⇒ T` then `extend Γ S ⊢ shift 1 0 t ⇒ T`: adding a fresh
  -- binder preserves typability, shifting the term by one. The type is
  -- UNCHANGED (the fresh binder is not in the term's scope).
  --
  -- OPEN OBLIGATION: the `⇒-var` case is the definitional lookup law, but
  -- the binder cases need the context-extension to commute with the
  -- Π/λ binder, which the flat prepend does not do. The standard fix is a
  -- context morphism (a `Fin` map); see proof/README.md.
  ------------------------------------------------------------------------

  -- Shifting a branch body at the branch's arity.
  shiftBranchBody : Branch → Branch
  shiftBranchBody (cn , ar , b) = cn , ar , shift 1 ar b

  postulate
    weaken⇒ : ∀ {Γ t T S} → Γ ⊢ t ⇒ T → extend Γ S ⊢ shift 1 0 t ⇒ T

  postulate
    weaken⇐ : ∀ {Γ t T S} → Γ ⊢ t ⇐ T → extend Γ S ⊢ shift 1 0 t ⇐ T

  ------------------------------------------------------------------------
  -- Substitution.
  --
  -- If `extend Γ A ⊢ t ⇒ T` and `Γ ⊢ a ⇐ A`, then `Γ ⊢ substT 0 a t ⇒ substT 0 a T`.
  --
  -- The well-formedness of the context is required for the `⇒-var` cases.
  ------------------------------------------------------------------------

  postulate
    subst⇒ :
      ∀ {Γ t T A a}
      → WfCtx (extend Γ A)
      → extend Γ A ⊢ t ⇒ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇒ substT 0 a T

  postulate
    subst⇐ :
      ∀ {Γ t T A a}
      → WfCtx (extend Γ A)
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
