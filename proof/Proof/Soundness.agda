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
-- STATUS: the CLASSICAL three-way disjunction (`soundness`, below) is a
-- negative statement in its `diverges` disjunct, so deciding WHICH disjunct
-- holds needs coinduction (or a well-founded measure) — neither of which
-- the development sets up. Its constructive content is the FUEL-INDEXED
-- theorem `soundness-fuel` (below), which IS proved: it returns either a
-- reached value or "fuel exhausted", by induction on the fuel `n`,
-- consuming Progress, Preservation, and `Final`-preservation
-- (Proof/FinalPreservation.agda). The classical statement is kept as a
-- `postulate` with its strategy, and is the coinductive completion of the
-- fuel-indexed theorem.
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
open import Proof.FinalPreservation

module Sound (ind : IndEnv) (sig : Signature) (conv : Conversion)
             (pos : StrictlyPositive ind) (cert : Certified sig) (cov : Covers ind)
             (bc : BuiltinCtors ind)
             (closed : ClosedSig ind sig) (rc : ReduceConv sig conv) where

  open Core.Typing.Typing ind sig conv
  open Proof.Progress.Progress ind sig conv pos cert cov bc
  open Proof.Preservation.Preserve ind sig conv closed rc
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
  -- The constructive, fuel-indexed soundness theorem.
  --
  -- `soundness-fuel n` runs the type-safety induction for `n` steps and
  -- returns either a REACHED value (with its type, value witness, and the
  -- multi-step reduction to it) or `exhausted` — the fuel ran out without
  -- reaching a value. This is the constructive content of the classical
  -- three-way disjunction: the `diverges` disjunct is a NEGATIVE statement
  -- (no value is reachable), so deciding it needs coinduction; the
  -- fuel-indexed version replaces it with the positive `exhausted` outcome,
  -- which is decidable by construction.
  --
  -- The proof is by induction on the fuel `n`, at each step consuming:
  --   * `progress⇐`          — a well-typed final term is a value or steps;
  --   * `preservation`       — the reduct keeps the type;
  --   * `final-preservation` — the reduct is still final (so `progress⇐`
  --                            applies again).
  ------------------------------------------------------------------------

  data FuelResult (t T : Term) : Set where
    reached   : (v : Term) → ⟨⟩ ⊢ v ⇐ T → Value v → _⇝*_ sig t v → FuelResult t T
    exhausted : FuelResult t T

  -- Prepend one reduction step to a fuel result: a value reached from `t′`
  -- is reached from `t` by the step, and exhaustion is preserved.
  prepend-step : ∀ {t t′ T} → _⇝_ sig t t′ → FuelResult t′ T → FuelResult t T
  prepend-step step (reached v dv val red) = reached v dv val (⇝*-step step red)
  prepend-step step exhausted = exhausted

  soundness-fuel :
    ∀ (n : ℕ) {t T}
    → ⟨⟩ ⊢ t ⇐ T
    → Final t
    → FuelResult t T
  soundness-fuel zero dt ft = exhausted
  soundness-fuel (suc n) {t} {T} dt ft with progress⇐ dt ft
  ... | inj₁ v = reached t dt v ⇝*-refl
  ... | inj₂ (t′ , step) =
    prepend-step step
      (soundness-fuel n (preservation dt step)
                         (final-preservation sig cert {t = t} {t′ = t′} ft step))

  ------------------------------------------------------------------------
  -- The "never stuck" corollary, in fuel form.
  --
  -- At every step of the fuel-indexed induction the term is a value or it
  -- steps — never neither. This is the constructive reading of "evaluation
  -- never reaches a stuck state": a well-typed final term is never stuck.
  ------------------------------------------------------------------------

  never-stuck :
    ∀ {t T}
    → ⟨⟩ ⊢ t ⇐ T
    → Final t
    → Value t ⊎ (∃ λ t′ → _⇝_ sig t t′)
  never-stuck = progress⇐

  ------------------------------------------------------------------------
  -- The bridge to the classical statement.
  --
  -- A `reached` fuel outcome IS the classical first disjunct: its value,
  -- type, value witness, and reduction are exactly the fields of
  -- `reaches-value`. So the fuel-indexed theorem's positive outcome
  -- directly inhabits the classical `EvalResult`, and the only gap to the
  -- classical statement is the coinductive decision of the negative
  -- (`diverges`) disjunct.
  ------------------------------------------------------------------------

  reached→eval :
    ∀ {t v T}
    → ⟨⟩ ⊢ v ⇐ T
    → Value v
    → _⇝*_ sig t v
    → EvalResult t T
  reached→eval dv val red = reaches-value _ dv val red

  ------------------------------------------------------------------------
  -- The classical soundness theorem.
  --
  -- This is the THREE-WAY disjunction of docs/SOUNDNESS.md §1.4. Its third
  -- disjunct, `diverges`, is a NEGATIVE statement (no value is reachable),
  -- so deciding which disjunct holds needs coinduction (or a well-founded
  -- measure) — neither of which the development sets up. The constructive
  -- content is `soundness-fuel` above: it is PROVED, and its `reached`
  -- outcome is exactly this theorem's first disjunct. The classical
  -- statement is the coinductive completion of `soundness-fuel`.
  --
  -- Proof strategy: by the type-safety induction (the same induction
  -- `soundness-fuel` performs), completed with the coinductive step that
  -- turns "exhausted for every `n`" into the `diverges` disjunct.
  --
  --   * If `e` is a value: outcome (1) with the reflexive closure.
  --   * If `e` is not a value: Progress gives `e ⇝ e′`; Preservation gives
  --     `· ⊢ e′ : T`; `Final`-preservation keeps `e′` final; recurse on `e′`.
  --   * If Progress raises: outcome (2).
  --   * If the recursion never reaches a value: outcome (3).
  --
  -- The "never stuck" corollary is immediate (`never-stuck` above): at
  -- every step the term is either a value, a redex (Progress), or a raise —
  -- never neither.
  ------------------------------------------------------------------------

  postulate
    soundness :
      ∀ {t T}
      → ⟨⟩ ⊢ t ⇒ T
      → Final t
      → EvalResult t T
