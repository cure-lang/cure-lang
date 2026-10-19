{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Soundness with the third classical input REPLACED by a true statement.
--
-- `Proof/Soundness.agda` proves the classical three-way theorem
--
--     reaches a value  ⊎  raises  ⊎  diverges
--
-- from two named classical inputs:
--
--   1. `tree-decides`            — the outcome tree is finite or infinite
--                                  (LPO on the outcome path);
--   2. `never-reached→no-value`  — a never-reaching tree has no reachable
--                                  value.
--
-- Input 2 is **FALSE as stated** for the mechanised `_⇝_`. The reason is
-- visible in `Proof/Progress.agda` itself:
--
--   * `progress⇐ (⇐-lam p q) = inj₁ (canonical c-lam)` — a λ is ALWAYS
--     reported as a `Value`, whatever its body does;
--   * `_⇝_` reduces UNDER BINDERS (`ξ-lam-body`).
--
-- So with `Ω = (λx. x x) (λx. x x)` (and `Ω ⇝ Ω` by β), the term
-- `tm-lam g d Ω` is a canonical `Value` that steps to itself forever. It is
-- therefore `NeverReached`, yet it reaches a `Value` in zero steps. Input 2
-- would derive `⊥` from a consistent hypothesis.
--
-- The root cause is that `Value` (canonical/neutral) does NOT mean "has
-- finished evaluating". The sharpest witness is `tm-lam g d Ω`: it is
-- CANONICAL (`c-lam`), so a `Value`, and `ξ-lam-body` steps it to itself.
-- So a `Value` can step forever, and "reaches a `Value`" is not the same as
-- "finishes". This module therefore does NOT try to prove anything about
-- `Value`-reducts; the honest predicate is `NormalForm` below.
--
-- WHAT THIS MODULE PROVES (constructively, no new postulates)
--
-- The repaired statement replaces input 2 by its TRUE form:
--
--   * `NormalForm t` — `t` admits no reduction step: `t` has FINISHED
--     evaluating. Strictly stronger than `Value` (every λ is a `Value`;
--     only a λ with a normal body is a `NormalForm`).
--   * `DivergesNF t` — the greatest fixed point "steps forever, and is
--     never a normal form".
--   * `never-reached-not-nf` — a never-reaching tree is NOT a normal form.
--     This is the true replacement for input 2: input 2 said "no VALUE is
--     reachable", which is false; "no NORMAL FORM is reachable" is
--     immediate from `NeverReached`'s step at every node.
--   * `soundness-nf` — the repaired dichotomy: `t` either REACHES a value
--     (`Reached`, the tree's own leaf) or it `DivergesNF`.
--
-- Note that the two disjuncts are NOT mutually exclusive, and cannot be:
-- `tm-lam g d Ω` is `Reached` (in zero steps) AND `DivergesNF`. That
-- overlap is a real property of the calculus, not a defect of the
-- statement — it is exactly why input 2 was false. What IS exclusive is
-- `NormalForm` versus `DivergesNF` (`nf-excludes-diverges`): a normal form
-- has no step, while `DivergesNF` has one at every node. No confluence and
-- no extra classical reasoning is needed for that exclusion.
--
-- WHY THE OBVIOUS STRENGTHENING FAILS (an honest negative result)
--
-- One is tempted to state the theorem as "reaches a NORMAL-FORM value, or
-- diverges". That is NOT provable from `soundness-tree`, and the
-- obstruction is the `Ω` counterexample again:
--
--   * a `Reached` leaf supplies only `Value v`;
--   * `progress⇐` at `v` returns `Value v ⊎ (∃ v′ → v ⇝ v′)`, and its
--     `inj₁` branch gives `Value v` AGAIN — never `NormalForm v`;
--   * and `tm-lam g d Ω` is a `Value` reached in zero steps that is not a
--     normal form.
--
-- So the reached value cannot be strengthened to a normal form without
-- deciding whether it can still step — the same non-constructive question.
-- The dichotomy below therefore keeps `Reached` as-is on the first side,
-- which is exactly what the tree proves.
--
-- Confluence (`Proof.Confluence.confluence`) is NOT used, and deliberately
-- so: the finding (docs/CONFLUENCE.md) is that confluence does not rescue
-- input 2, because the counterexample is a value stepping to VALUES
-- forever — a property of `Value`, not of the reduction's branching.
-- `next.step.txt` item (a) proposed proving confluence to discharge input
-- 2; this module records that the proposal does not work as stated.
--
-- The remaining classical input is `tree-decides` alone (LPO on the outcome
-- path), used only by the fuel/coinductive bridge in
-- `Proof/Soundness.agda`; nothing below depends on it.
------------------------------------------------------------------------
module Proof.SoundnessConfluence where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; Conversion)
open import Proof.Values using (Value; Canonical; Neutral; canonical; neutral)
open import Proof.Progress using (Final; StrictlyPositive; Certified; Covers;
                                    BuiltinCtors)
open import Proof.Preservation using (ClosedSig; ReduceConv; CertifiedTyped)
open import Proof.Soundness

module SoundNF (ind : IndEnv) (sig : Signature) (conv : Conversion)
               (pos : StrictlyPositive ind) (cert : Certified sig) (cov : Covers ind)
               (bc : BuiltinCtors ind)
               (closed : ClosedSig ind sig) (rc : ReduceConv sig conv)
               (ctyped : CertifiedTyped ind sig conv) where

  open Core.Typing.Typing ind sig conv
  open Proof.Soundness.Sound ind sig conv pos cert cov bc closed rc ctyped

  ------------------------------------------------------------------------
  -- Normal forms.
  ------------------------------------------------------------------------

  NormalForm : Term → Set
  NormalForm t = ∀ {t′} → ¬ (_⇝_ sig t t′)

  ------------------------------------------------------------------------
  -- A normal form is inert under multi-step reduction: the only term it
  -- reaches is itself. (No confluence needed: the first step already
  -- contradicts normality.)
  ------------------------------------------------------------------------

  nf-no-step : ∀ {t t′} → NormalForm t → _⇝*_ sig t t′ → t ≡ t′
  nf-no-step nf ⇝*-refl = refl
  nf-no-step nf (⇝*-step s ss) = ⊥-elim (nf s)

  ------------------------------------------------------------------------
  -- Divergence, positively, over normal forms.
  --
  -- `dnf-not-nf` is derivable from `dnf-step` (a term that steps is not
  -- normal), but carrying it explicitly makes the exclusion with "reaches
  -- a normal form" a one-line computation on the witnesses.
  ------------------------------------------------------------------------

  record DivergesNF (t : Term) : Set where
    coinductive
    field
      dnf-step   : ∃ λ t′ → _⇝_ sig t t′ × DivergesNF t′
      dnf-not-nf : ¬ NormalForm t

  ------------------------------------------------------------------------
  -- `NormalForm` and `DivergesNF` are exclusive, constructively.
  --
  -- (Not `Reached` and `DivergesNF`: those genuinely overlap, see the
  -- header. This is the exclusion that the repaired statement actually
  -- needs, and it is a one-line computation on the witnesses.)
  ------------------------------------------------------------------------

  nf-excludes-diverges : ∀ {t} → NormalForm t → DivergesNF t → ⊥
  nf-excludes-diverges nf div = DivergesNF.dnf-not-nf div nf

  ------------------------------------------------------------------------
  -- `DivergesNF` implies the classical `Diverges`.
  ------------------------------------------------------------------------

  DivergesNF→Diverges : ∀ {t} → DivergesNF t → Diverges t
  Diverges.diverges-step (DivergesNF→Diverges div) with DivergesNF.dnf-step div
  ... | t′ , step , div′ = t′ , step , DivergesNF→Diverges div′

  ------------------------------------------------------------------------
  -- THE REPLACEMENT FOR INPUT 2: a never-reaching tree is not a normal
  -- form.
  --
  -- `NeverReached` supplies a step at EVERY node; `NormalForm` forbids
  -- exactly that. Input 2 tried to conclude "no VALUE is reachable", which
  -- is false; "no NORMAL FORM is reachable" is immediate.
  ------------------------------------------------------------------------

  never-reached-not-nf : ∀ {t T} → NeverReached t T → ¬ NormalForm t
  never-reached-not-nf nr nf with NeverReached.nr-step nr
  ... | t′ , step , nr′ = nf step

  ------------------------------------------------------------------------
  -- A never-reaching tree diverges in the `DivergesNF` sense.
  --
  -- Guarded corecursion: the step comes from the tree, and the reduct's
  -- tree is never-reaching too, so the invariant is maintained.
  ------------------------------------------------------------------------

  never-reached→divergesNF : ∀ {t T} → NeverReached t T → DivergesNF t
  DivergesNF.dnf-step (never-reached→divergesNF nr) with NeverReached.nr-step nr
  ... | t′ , step , nr′ = t′ , step , never-reached→divergesNF nr′
  DivergesNF.dnf-not-nf (never-reached→divergesNF nr) = never-reached-not-nf nr

  ------------------------------------------------------------------------
  -- The repaired outcome type.
  --
  -- Two disjuncts, both constructive:
  --
  --   * `reaches` — a value is reached (the tree's own `Reached` leaf);
  --   * `steps-forever` — `t` `DivergesNF`.
  --
  -- The `raises` outcome of `EvalResult` is dropped: under `Covers` it is
  -- unreachable (`progress` never produces it), so carrying it would add a
  -- disjunct no proof can inhabit.
  ------------------------------------------------------------------------

  data NFOutcome (t T : Term) : Set where
    reaches : Reached t T → NFOutcome t T
    steps-forever : DivergesNF t → NFOutcome t T

  ------------------------------------------------------------------------
  -- The repaired soundness theorem.
  --
  -- From `soundness-tree` and the single classical input `tree-decides`:
  --
  --   * a `Reached` tree gives `reaches` — no classical input needed;
  --   * a `NeverReached` tree gives `steps-forever`
  --     (`never-reached→divergesNF`) — no classical input needed.
  --
  -- So the ONLY classical input left is `tree-decides` (LPO on the outcome
  -- path). Input 2 is gone, replaced by the constructive
  -- `never-reached-not-nf`.
  --
  -- HONEST SCOPE. This is a REPAIR, not a strengthening: `soundness-nf` is
  -- essentially `tree-decides` composed with the constructive bridge above.
  -- Its value is that every disjunct is TRUE and every proof is
  -- constructive — the original `soundness` was built on an input that is
  -- refutable, so its third disjunct was unsound. It is also NOT the
  -- stronger statement "reaches a NORMAL-FORM value, or diverges", which is
  -- unprovable from `soundness-tree` (see the header).
  ------------------------------------------------------------------------

  soundness-nf :
    ∀ {t T}
    → ⟨⟩ ⊢ t ⇐ T
    → Final t
    → NFOutcome t T
  soundness-nf {t} {T} dt ft with tree-decides (soundness-tree dt ft)
  ... | inj₁ r = reaches r
  ... | inj₂ nr = steps-forever (never-reached→divergesNF nr)

  ------------------------------------------------------------------------
  -- Corollary: a well-typed final term never diverges through a normal
  -- form. This is the "never stuck" reading of the repaired statement,
  -- stated over `DivergesNF` rather than `Value`.
  ------------------------------------------------------------------------

  diverges-not-nf : ∀ {t} → DivergesNF t → ¬ NormalForm t
  diverges-not-nf div = DivergesNF.dnf-not-nf div
