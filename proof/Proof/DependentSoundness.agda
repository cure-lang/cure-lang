{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Constructive NATIVE specification safety, not kernel refinement.
-- One fixed goal survives every selected or supplied finite path.
-- Exhaustion is not divergence; Value is not a normal-form assertion.
-- No classical outcome decision or no-reachable-value claim is used.
------------------------------------------------------------------------
module Proof.DependentSoundness where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Signature using (IndEnv)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Reduction
import Core.DependentTyping as Native
open import Proof.Progress using (Final; BodiesFinal)
import Proof.FinalPreservation as Finality
open import Proof.DependentDataConversion using (DataComponents)
open import Proof.DependentLiteralPreservation using (BuiltinShapes)
import Proof.DependentProgress as Progress
import Proof.DependentSubjectReduction as Subject
import Proof.DependentObservation as Observation

-- These fields are independently checkable specification evidence, not
-- progress/preservation callbacks supplied by the consumer.
record Specification (ind : IndEnv) (sig : Signature) (conv : Conversion) : Set where
  field
    signature-valid : Native.Typing.SignatureValid ind sig conv
    data-components : DataComponents conv
    reduction-converts : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u
    global-bodies-final : BodiesFinal sig
    builtin-shapes : BuiltinShapes ind

module Sound (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (spec : Specification ind sig conv) where
  open Native.Typing ind sig conv
  open Specification spec
  module P = Subject.Preserve ind sig conv signature-valid data-components
    reduction-converts global-bodies-final builtin-shapes
  module G = Progress.Progress ind sig conv
  module O = Observation.Policy sig

  -- Syntax-produced witnesses are checked reductions/values. If the
  -- partial policy cannot choose, the native progress THEOREM does.
  observe : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → O.Choice t
  observe {t = t} typed final with O.candidate t
  ... | just choice = choice
  ... | nothing = G.progress⇐ typed final

  next-typed : ∀ {t u T} → ⟨⟩ ⊢ t ⇐ T → Final t → _⇝_ sig t u → ⟨⟩ ⊢ u ⇐ T
  next-typed = P.preservation⇐ wf[]
  next-final : ∀ {t u} → Final t → _⇝_ sig t u → Final u
  next-final = Finality.final-preservation sig global-bodies-final

  record SafeState (t T : Term) : Set where
    field
      typed : ⟨⟩ ⊢ t ⇐ T
      final : Final t
      ready : O.Choice t

  -- Safety holds along ANY supplied finite specification path, not just
  -- the path chosen by observe. No evaluation strategy completeness claim.
  trace-safe : ∀ {t u T} → ⟨⟩ ⊢ t ⇐ T → Final t → _⇝*_ sig t u → SafeState u T
  trace-safe typed final path = record
    { typed = typed′ ; final = final′ ; ready = observe typed′ final′ }
    where
      typed′ = P.preservation-star⇐ wf[] typed final path
      final′ = Finality.final-preservation-star sig global-bodies-final final path

  never-stuck : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → O.Choice t
  never-stuck = observe

  Reached : Term → Term → Set
  Reached t T = ∃ λ v → (⟨⟩ ⊢ v ⇐ T) × Final v × Value v × _⇝*_ sig t v

  data FuelResult (t T : Term) : Set where
    reached : Reached t T → FuelResult t T
    -- The current prefix endpoint is still typed and final. It may
    -- ALREADY be a value: zero fuel performs no additional observation.
    exhausted : ∀ u → ⟨⟩ ⊢ u ⇐ T → Final u → _⇝*_ sig t u → FuelResult t T

  data Status : Set where
    reached-value exhausted-fuel : Status
  status : ∀ {t T} → FuelResult t T → Status
  status (reached witness) = reached-value
  status (exhausted u typed final path) = exhausted-fuel
  endpoint : ∀ {t T} → FuelResult t T → Term
  endpoint (reached (v , rest)) = v
  endpoint (exhausted u typed final path) = u

  prepend-step : ∀ {t u T} → _⇝_ sig t u → FuelResult u T → FuelResult t T
  prepend-step step (reached (v , typed , final , value , path)) =
    reached (v , typed , final , value , ⇝*-step step path)
  prepend-step step (exhausted u typed final path) =
    exhausted u typed final (⇝*-step step path)

  soundness-fuel : ∀ (fuel : ℕ) {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → FuelResult t T
  soundness-fuel zero {t = t} typed final = exhausted t typed final ⇝*-refl
  soundness-fuel (suc fuel) {t = t} typed final with observe typed final
  ... | inj₁ value = reached (t , typed , final , value , ⇝*-refl)
  ... | inj₂ (u , step) =
    prepend-step step (soundness-fuel fuel (next-typed typed final step) (next-final final step))

  record EvalTree (t T : Term) : Set where
    coinductive
    field
      typed : ⟨⟩ ⊢ t ⇐ T
      final : Final t
      outcome : Reached t T ⊎ (∃ λ u → _⇝_ sig t u × EvalTree u T)

  mutual
    tree-outcome : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t
      → Reached t T ⊎ (∃ λ u → _⇝_ sig t u × EvalTree u T)
    tree-outcome {t = t} typed final with observe typed final
    ... | inj₁ value = inj₁ (t , typed , final , value , ⇝*-refl)
    ... | inj₂ (u , step) =
      inj₂ (u , step , soundness-tree (next-typed typed final step) (next-final final step))

    soundness-tree : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → EvalTree t T
    EvalTree.typed (soundness-tree typed final) = typed
    EvalTree.final (soundness-tree typed final) = final
    EvalTree.outcome (soundness-tree typed final) = tree-outcome typed final

  truncate : ∀ (fuel : ℕ) {t T} → EvalTree t T → FuelResult t T
  truncate zero {t = t} tree = exhausted t (EvalTree.typed tree) (EvalTree.final tree) ⇝*-refl
  truncate (suc fuel) tree with EvalTree.outcome tree
  ... | inj₁ witness = reached witness
  ... | inj₂ (u , step , rest) = prepend-step step (truncate fuel rest)

  soundness-fuel≡truncate : ∀ (fuel : ℕ) {t T} (typed : ⟨⟩ ⊢ t ⇐ T) (final : Final t)
    → soundness-fuel fuel typed final ≡ truncate fuel (soundness-tree typed final)
  soundness-fuel≡truncate zero typed final = refl
  soundness-fuel≡truncate (suc fuel) typed final with observe typed final
  ... | inj₁ value = refl
  ... | inj₂ (u , step) =
    cong (prepend-step step)
      (soundness-fuel≡truncate fuel (next-typed typed final step) (next-final final step))

  -- A supplied infinite raw path can be annotated constructively. This
  -- is NOT a decision that the selected outcome tree is infinite, and
  -- does not assert that no Value is reachable along another path.
  record Diverges (t : Term) : Set where
    coinductive
    field
      step : ∃ λ u → _⇝_ sig t u × Diverges u

  record TypedDiverges (t T : Term) : Set where
    coinductive
    field
      typed : ⟨⟩ ⊢ t ⇐ T
      final : Final t
      step : ∃ λ u → _⇝_ sig t u × TypedDiverges u T

  annotate-divergence : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → Diverges t → TypedDiverges t T
  TypedDiverges.typed (annotate-divergence typed final path) = typed
  TypedDiverges.final (annotate-divergence typed final path) = final
  TypedDiverges.step (annotate-divergence typed final path) with Diverges.step path
  ... | u , step , rest =
    u , step , annotate-divergence (next-typed typed final step) (next-final final step) rest
