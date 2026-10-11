{-# OPTIONS --guardedness #-}
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
-- NEGATIVE statement in its `diverges` disjunct, so deciding WHICH disjunct
-- holds needs coinduction (or a well-founded measure). This module supplies
-- BOTH:
--
--   * the FUEL-INDEXED theorem `soundness-fuel` — the bounded unfolding of
--     the outcome, proved by induction on the fuel `n`;
--   * the COINDUCTIVE theorem `soundness-tree` — the outcome as a
--     (possibly infinite) tree, proved by guarded corecursion, with
--     divergence given POSITIVELY by the greatest fixed point `Diverges`.
--
-- The classical statement is the (non-constructive) COLLAPSE of the tree
-- into a `data` disjunction: extracting the finite `reaches-value` branch or
-- the infinite `diverges` branch requires deciding whether the tree is
-- finite, which (for a non-deterministic reduction relation) is not
-- constructive. The coinductive `soundness-tree` is the constructive
-- replacement; the classical `soundness` is kept as a `postulate` whose
-- proof is exactly that collapse.
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
  -- The possible outcomes of evaluating a closed term (the classical
  -- three-way disjunction, docs/SOUNDNESS.md §1.4).
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
  -- reaching a value. This is the BOUNDED unfolding of the outcome tree
  -- (`soundness-tree`, below): it is the tree truncated at depth `n`.
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
      (soundness-fuel n (preservation ft dt step)
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
  -- Divergence, POSITIVELY.
  --
  -- The classical `diverges` disjunct is a NEGATIVE statement ("no value is
  -- reachable"). Its constructive counterpart is the GREATEST fixed point
  -- of "can take a step": a term diverges when it can always step. This is
  -- a coinductive record, so an infinite reduction sequence is a FINITE
  -- proof object (a cyclic one), and no decision about reachability is
  -- needed.
  ------------------------------------------------------------------------

  record Diverges (t : Term) : Set where
    coinductive
    field
      diverges-step : ∃ λ t′ → _⇝_ sig t t′ × Diverges t′

  -- `Diverges` is a tree that never reaches a value: every node steps.
  -- This is the coinductive predicate on the OUTCOME TREE corresponding to
  -- `Diverges` on terms, and the two are inter-derivable (below).
  record NeverReached (t T : Term) : Set where
    coinductive
    field
      nr-step : ∃ λ t′ → _⇝_ sig t t′ × NeverReached t′ T

  ------------------------------------------------------------------------
  -- The constructive outcome tree.
  --
  -- `EvalTree t T` is the (possibly infinite) tree of evaluation steps from
  -- `t`:
  --
  --   * a node is `Reached` when `t` reduces to a well-typed value (the
  --     finite, terminating outcome); or
  --   * a node is `Stepped` when `t` steps to `t′` and the tree continues
  --     at `t′`.
  --
  -- This is a coinductive record, so an INFINITE evaluation is a finite
  -- (cyclic) proof object — exactly the constructive replacement for the
  -- negative `diverges` disjunct. The classical `EvalResult` is the
  -- collapse of this tree into a `data` disjunction, which requires
  -- deciding whether the tree is finite.
  ------------------------------------------------------------------------

  Reached : Term → Term → Set
  Reached t T = ∃ λ v → ⟨⟩ ⊢ v ⇐ T × Value v × _⇝*_ sig t v

  record EvalTree (t T : Term) : Set where
    coinductive
    field
      outcome : Reached t T ⊎ (∃ λ t′ → _⇝_ sig t t′ × EvalTree t′ T)

  ------------------------------------------------------------------------
  -- The coinductive soundness theorem.
  --
  -- PROVED by guarded corecursion: at each node, Progress decides whether
  -- the term is a value (the `Reached` leaf) or steps (the `Stepped` node),
  -- and the recursive call — under the `Stepped` constructor — is guarded.
  -- The reduct keeps its type (Preservation) and stays final
  -- (`final-preservation`), so the recursion is well-typed at every node.
  --
  -- This is the constructive content of §1.4: a well-typed final term
  -- either reaches a value (a FINITE tree) or steps forever (an INFINITE
  -- tree). The `raises` outcome never occurs here, because `Covers` makes
  -- the ι coverage guard unreachable (Progress always returns a value or a
  -- step).
  ------------------------------------------------------------------------

  -- The root outcome of the tree, as a standalone function, so the fuel
  -- truncation lemma can unfold it definitionally.
  mutual
    tree-outcome :
      ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t
      → Reached t T ⊎ (∃ λ t′ → _⇝_ sig t t′ × EvalTree t′ T)
    tree-outcome {t} dt ft with progress⇐ dt ft
    ... | inj₁ v = inj₁ (t , dt , v , ⇝*-refl)
    ... | inj₂ (t′ , step) =
      inj₂ (t′ , step ,
            soundness-tree (preservation ft dt step)
                           (final-preservation sig cert {t = t} {t′ = t′} ft step))

    soundness-tree :
      ∀ {t T}
      → ⟨⟩ ⊢ t ⇐ T
      → Final t
      → EvalTree t T
    EvalTree.outcome (soundness-tree dt ft) = tree-outcome dt ft

  ------------------------------------------------------------------------
  -- `Diverges` and the outcome tree's infinite spine coincide.
  --
  -- A term diverges (`Diverges`) precisely when its outcome tree never
  -- reaches a value (`NeverReached`). Both directions are guarded
  -- corecursions: the term-level step and the tree-level step are the same
  -- reduction, so the two greatest fixed points are the same object.
  ------------------------------------------------------------------------

  -- A never-reaching tree gives a divergence witness: forget the type.
  never-reached→diverges : ∀ {t T} → NeverReached t T → Diverges t
  Diverges.diverges-step (never-reached→diverges nr) with NeverReached.nr-step nr
  ... | t′ , step , nr′ = t′ , step , never-reached→diverges nr′

  -- A divergence witness gives a never-reaching tree, given the typing that
  -- keeps the recursion well-typed (`progress⇐` never returns a value).
  diverges→never-reached : ∀ {t T} → Diverges t → ⟨⟩ ⊢ t ⇐ T → Final t → NeverReached t T
  NeverReached.nr-step (diverges→never-reached div dt ft) with Diverges.diverges-step div
  ... | t′ , step , div′ = t′ , step ,
    diverges→never-reached div′ (preservation ft dt step)
                              (final-preservation sig cert {t = _} {t′ = t′} ft step)

  ------------------------------------------------------------------------
  -- The fuel-indexed run is the depth-`n` truncation of the tree.
  --
  -- `soundness-fuel n` and `soundness-tree` are two views of the same
  -- object: the tree is the full (possibly infinite) outcome, and the
  -- fuel-indexed run is its truncation to depth `n`. This makes precise the
  -- claim that the fuel-indexed theorem is the BOUNDED unfolding of the
  -- coinductive one.
  ------------------------------------------------------------------------

  -- Truncate the outcome tree to depth `n`.
  truncate : ∀ (n : ℕ) {t T} → EvalTree t T → FuelResult t T
  truncate zero tree = exhausted
  truncate (suc n) tree with EvalTree.outcome tree
  ... | inj₁ (v , dv , val , red) = reached v dv val red
  ... | inj₂ (t′ , step , tree′) = prepend-step step (truncate n tree′)

  -- The two agree: `soundness-fuel` is `soundness-tree` truncated.
  soundness-fuel≡truncate :
    ∀ (n : ℕ) {t T} (dt : ⟨⟩ ⊢ t ⇐ T) (ft : Final t)
    → soundness-fuel n dt ft ≡ truncate n (soundness-tree dt ft)
  soundness-fuel≡truncate zero dt ft = refl
  soundness-fuel≡truncate (suc n) {t} {T} dt ft with progress⇐ dt ft
  ... | inj₁ v = refl
  ... | inj₂ (t′ , step) =
    cong (prepend-step step)
         (soundness-fuel≡truncate n (preservation ft dt step)
                                    (final-preservation sig cert {t = t} {t′ = t′} ft step))

  ------------------------------------------------------------------------
  -- The bridge to the classical statement.
  --
  -- A `Reached` node IS the classical first disjunct: its value, type,
  -- value witness, and reduction are exactly the fields of `reaches-value`.
  ------------------------------------------------------------------------

  reached→eval :
    ∀ {t v T}
    → ⟨⟩ ⊢ v ⇐ T
    → Value v
    → _⇝*_ sig t v
    → EvalResult t T
  reached→eval dv val red = reaches-value _ dv val red

  -- A `Reached` node of the outcome tree yields the classical first
  -- disjunct directly.
  tree-reached→eval :
    ∀ {t T} → Reached t T → EvalResult t T
  tree-reached→eval (v , dv , val , red) = reaches-value v dv val red

  ------------------------------------------------------------------------
  -- The classical soundness theorem.
  --
  -- This is the THREE-WAY disjunction of docs/SOUNDNESS.md §1.4. Its third
  -- disjunct, `diverges`, is a NEGATIVE statement (no value is reachable),
  -- so deciding which disjunct holds needs coinduction (or a well-founded
  -- measure). The constructive content is `soundness-tree` above: it is
  -- PROVED, and collapsing it into this `data` disjunction requires
  -- deciding whether the outcome tree is finite — not constructive for a
  -- non-deterministic reduction relation (`_⇝_` is not deterministic:
  -- `(λx. b) a` can both β-reduce and reduce under the λ).
  --
  -- Proof strategy: the collapse of `soundness-tree`. At each node:
  --   * a `Reached` node gives outcome (1) (`tree-reached→eval`);
  --   * a `Stepped` node recurses;
  --   * the `raises` outcome (2) is the coverage guard, unreachable under
  --     `Covers`;
  --   * if the tree has no `Reached` node, its infinite `Stepped` spine is
  --     a `Diverges` witness, giving outcome (3).
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
