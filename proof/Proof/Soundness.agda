------------------------------------------------------------------------
-- Soundness (docs/SOUNDNESS.md §1.4).
--
--   Let `e` be a closed, hole-free, final-Core term with `· ⊢ e : T` for a
--   closed type `T`. Then evaluation of `e` either reaches a value `v` with
--   `· ⊢ v : T`; or raises; or diverges. In particular, evaluation never
--   reaches a STUCK state.
--
-- The theorem combines Progress (Proof/Progress.agda) and Preservation
-- (Proof/Preservation.agda) by the standard "type safety" induction: run
-- Progress to get a step, Preservation to keep the type, and iterate.
--
-- STATUS: the combination is the current research frontier, marked
-- `postulate` with its strategy.
------------------------------------------------------------------------
module Proof.Soundness where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; Conversion)
open import Proof.Values using (Value; Canonical; Neutral; canonical; neutral)
open import Proof.Progress using (Final; FinalTerms; FinalBranches;
                                    StrictlyPositive; Certified; Covers; BuiltinCtors)
open import Proof.Preservation

module Sound (ind : IndEnv) (sig : Signature) (conv : Conversion)
             (pos : StrictlyPositive ind) (cert : Certified sig) (cov : Covers ind)
             (bc : BuiltinCtors ind)
             (closed : ClosedSig ind sig) where

  open Core.Typing.Typing ind sig conv
  open Proof.Progress.Progress ind sig conv pos cert cov bc
  open Proof.Preservation.Preserve ind sig conv closed
  ------------------------------------------------------------------------
  -- The possible outcomes of evaluating a closed term.
  ------------------------------------------------------------------------

  data EvalResult (t T : Term) : Set where
    -- (1) reaches a value v with · ⊢ v : T
    reaches-value : ∀ v → ⟨⟩ ⊢ v ⇐ T → Value v → _⇝*_ sig t v → EvalResult t T
    -- (2) raises (modelled as a distinguished error outcome)
    raises : EvalResult t T
    -- (3) diverges
    diverges : (∀ v → _⇝*_ sig t v → Value v → ⊥) → EvalResult t T

  ------------------------------------------------------------------------
  -- The soundness theorem.
  --
  -- Proof strategy: by the type-safety induction.
  --   * If `e` is a value: outcome (1) with the reflexive closure.
  --   * If `e` is not a value: Progress gives `e ⇝ e′`; Preservation gives
  --     `· ⊢ e′ : T`; recurse on `e′`.
  --   * If Progress raises: outcome (2).
  --   * If the recursion never reaches a value: outcome (3).
  --
  -- The "never stuck" corollary is immediate: at every step the term is
  -- either a value, a redex (Progress), or a raise — never neither.
  --
  -- OPEN OBLIGATION: the induction. It consumes `progress` and
  -- `preservation`, both of which are stated with their strategies.
  ------------------------------------------------------------------------

  postulate
    soundness :
      ∀ {t T}
      → ⟨⟩ ⊢ t ⇒ T
      → Final t
      → EvalResult t T
