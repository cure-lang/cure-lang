{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Opt-in residual checking in a PROVED well-formed ambient context.
-- Inference and BOTH type kinds precede exact syntax or bounded equality.
-- No conversion witness or normalization callback is trusted as input.
------------------------------------------------------------------------
module Core.AmbientResidualAdmission where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)
open import Core.Syntax
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; Conversion)
open import Core.Reduction using (_⇝*_)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as Admission
import Core.ClosureEval as E
import Core.ResidualComparison as Compare
import Core.SyntaxEquality as Syntax
import Proof.ResidualConversion as EqualityProof
import Proof.FreshEnvironment as Fresh

-- The SAME data-only request and diagnostics; strict replay stays unchanged.
open import Core.NormalizingAdmission public using
  (Request; request; Rejection; Result; accepted; rejected; present;
   malformed-wire; unsupported-subject; inference-failed; unsupported-inferred;
   inferred-kind-failed; unsupported-goal; goal-kind-failed; distinct-forms; inconclusive)

data Basis (size : ℕ) (inferred goal : Term) : Set where
  exact : inferred ≡ goal → Basis size inferred goal
  normalized : Compare.EqualResidual size (Fresh.environment size) inferred goal → Basis size inferred goal
module Replay {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module C = Admission.Checked source-checked
  module N = C.W.N
  module D = C.W.G.D
  module R = C.W.R.R
  abstract
    basis-sound : ∀ {size inferred goal} → R.Supported size inferred → R.Supported size goal
      → Basis size inferred goal → Conversion._≈_ C.W.M.conversion inferred goal
    basis-sound {inferred = inferred} left right (exact refl) = Conversion.≈-refl C.W.M.conversion {t = inferred}
    basis-sound {size} left right (normalized equal) =
      subst₂ (Conversion._≈_ C.W.M.conversion) (Fresh.identity (R.scoped left)) (Fresh.identity (R.scoped right))
        (EqualityProof.Sound.conversion source-checked (Fresh.scoped size)
          (Fresh.source-scope (R.scoped left)) (Fresh.source-scope (R.scoped right)) (Fresh.denotes size) equal)

  record Checked {size : ℕ} (context : Ctx size) (query : Request) : Set where
    open Request query
    field
      context-valid : N.WellFormed context
      subject-supported : R.Supported size subject
      inferred : Term
      synthesized : N._⊢_⇒_ context subject inferred
      inferred-supported : R.Supported size inferred
      inferred-level : Level
      inferred-kind : N._⊢_⇒_ context inferred (tm-type inferred-level)
      goal-supported : R.Supported size goal
      goal-level : Level
      goal-kind : N._⊢_⇒_ context goal (tm-type goal-level)
      basis : Basis size inferred goal
    converts : Conversion._≈_ C.W.M.conversion inferred goal
    converts = basis-sound inferred-supported goal-supported basis
    admitted : N.Admitted context subject goal
    admitted = record
      { signature-valid = C.valid ; context-valid = context-valid
      ; term-scoped = R.scoped subject-supported ; goal-scoped = R.scoped goal-supported
      ; goal-level = goal-level ; goal-kind = goal-kind ; checked = N.⇐-infer synthesized converts }
    typed : N._⊢_⇒_ context subject goal
    typed = N.⇒-conv synthesized converts

  -- All positive evidence is retained before the comparison is selected.
  choose : ∀ {size} {context : Ctx size} {query} (fuel : ℕ) (inferred : Term)
    → (Basis size inferred (Request.goal query) → Checked context query) → Result (Checked context query)
  choose {size} {query = query} fuel inferred build with Syntax.equal? inferred (Request.goal query)
  ... | yes same = accepted (build (exact same))
  ... | no different with Compare.compare-with C.W.ind fuel size (Fresh.environment size) inferred (Request.goal query)
  ... | Compare.same equal = accepted (build (normalized equal))
  ... | Compare.distinct forms = rejected
    (distinct-forms (Compare.DistinctResidual.left-form forms) (Compare.DistinctResidual.right-form forms))
  ... | Compare.unknown side reason = rejected (inconclusive side reason)

  verify-in : ∀ {size} (context : Ctx size) → N.WellFormed context → ℕ → (query : Request)
    → Result (Checked context query)
  verify-in {size} context wf fuel query with R.supported? size (Request.subject query)
  ... | no invalid = rejected unsupported-subject
  ... | yes subject-supported with D.infer-wf context wf (Request.subject query) (Request.subject-recipe query)
  ... | nothing = rejected inference-failed
  ... | just (inferred , synthesized) with R.supported? size inferred
  ... | no invalid = rejected unsupported-inferred
  ... | yes inferred-supported with D.kind-wf context wf inferred (Request.inferred-kind-recipe query)
  ... | nothing = rejected inferred-kind-failed
  ... | just (inferred-level , inferred-kind) with R.supported? size (Request.goal query)
  ... | no invalid = rejected unsupported-goal
  ... | yes goal-supported with D.kind-wf context wf (Request.goal query) (Request.goal-kind-recipe query)
  ... | nothing = rejected goal-kind-failed
  ... | just (goal-level , goal-kind) = choose fuel inferred (λ basis → record
    { context-valid = wf ; subject-supported = subject-supported ; inferred = inferred ; synthesized = synthesized
    ; inferred-supported = inferred-supported ; inferred-level = inferred-level ; inferred-kind = inferred-kind
    ; goal-supported = goal-supported ; goal-level = goal-level ; goal-kind = goal-kind ; basis = basis })
