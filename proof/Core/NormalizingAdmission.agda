{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Optional CLOSED checking protocol. Inference and BOTH type kinds are
-- replayed before exact syntax or bounded normalized equality is used.
-- No conversion witness or normalization callback is trusted as input.
------------------------------------------------------------------------
module Core.NormalizingAdmission where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Universe using (Level)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Reduction using (_⇝*_)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as Admission
import Core.ClosureEval as E
import Core.NormalFormComparison as Compare
import Core.SyntaxEquality as Syntax
import Proof.NormalFormConversion as EqualityProof
import Proof.Progress as Final

record Request : Set where
  constructor request
  field
    subject : Term
    subject-recipe inferred-kind-recipe : Recipe
    goal : Term
    goal-kind-recipe : Recipe

data Basis (inferred goal : Term) : Set where
  exact : inferred ≡ goal → Basis inferred goal
  normalized : Compare.EqualNormal 0 [] inferred goal → Basis inferred goal
data Rejection : Set where
  malformed-wire : Rejection
  unsupported-subject inference-failed unsupported-inferred inferred-kind-failed
    unsupported-goal goal-kind-failed : Rejection
  distinct-forms : Term → Term → Rejection
  inconclusive : Compare.Side → E.Failure → Rejection
data Result (A : Set) : Set where
  accepted : A → Result A
  rejected : Rejection → Result A
present : ∀ {A} → Result A → Bool
present (accepted proof) = true
present (rejected reason) = false

module Replay {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module C = Admission.Checked source-checked
  module N = C.W.N
  module D = C.W.G.D
  module R = C.W.R.R
  abstract
    basis-sound : ∀ {inferred goal} → R.Supported 0 inferred → R.Supported 0 goal
      → Basis inferred goal → Conversion._≈_ C.W.M.conversion inferred goal
    basis-sound {inferred} left right (exact refl) = Conversion.≈-refl C.W.M.conversion {t = inferred}
    basis-sound left right (normalized equal) =
      EqualityProof.Sound.closed-conversion source-checked (R.scoped left) (R.scoped right) equal

  record Checked (query : Request) : Set where
    open Request query
    field
      subject-supported : R.Supported 0 subject
      inferred : Term
      synthesized : N._⊢_⇒_ ⟨⟩ subject inferred
      inferred-supported : R.Supported 0 inferred
      inferred-level : Level
      inferred-kind : N._⊢_⇒_ ⟨⟩ inferred (tm-type inferred-level)
      goal-supported : R.Supported 0 goal
      goal-level : Level
      goal-kind : N._⊢_⇒_ ⟨⟩ goal (tm-type goal-level)
      basis : Basis inferred goal
    converts : Conversion._≈_ C.W.M.conversion inferred goal
    converts = basis-sound inferred-supported goal-supported basis
    admitted : N.Admitted ⟨⟩ subject goal
    admitted = record
      { signature-valid = C.valid ; context-valid = N.wf[]
      ; term-scoped = R.scoped subject-supported ; goal-scoped = R.scoped goal-supported
      ; goal-level = goal-level ; goal-kind = goal-kind ; checked = N.⇐-infer synthesized converts }
    final : Final.Final subject
    final = R.final subject-supported
    trace-safe : ∀ {endpoint} → _⇝*_ C.W.sig subject endpoint → C.Sound.SafeState endpoint goal
    trace-safe = C.Sound.trace-safe (N.Admitted.checked admitted) final
    run : ℕ → C.Sound.FuelResult subject goal
    run fuel = C.Sound.soundness-fuel fuel (N.Admitted.checked admitted) final
    tree : C.Sound.EvalTree subject goal
    tree = C.Sound.soundness-tree (N.Admitted.checked admitted) final
    budgets-agree : ∀ fuel → run fuel ≡ C.Sound.truncate fuel tree
    budgets-agree fuel = C.Sound.soundness-fuel≡truncate fuel (N.Admitted.checked admitted) final

  -- All positive evidence is retained before the comparison is selected.
  choose : ∀ {query} (fuel : ℕ) (inferred : Term)
    → (Basis inferred (Request.goal query) → Checked query) → Result (Checked query)
  choose {query} fuel inferred build with Syntax.equal? inferred (Request.goal query)
  ... | yes same = accepted (build (exact same))
  ... | no different with Compare.compare fuel 0 [] inferred (Request.goal query)
  ... | Compare.same equal = accepted (build (normalized equal))
  ... | Compare.distinct forms = rejected
    (distinct-forms (Compare.DistinctNormal.left-form forms) (Compare.DistinctNormal.right-form forms))
  ... | Compare.unknown side reason = rejected (inconclusive side reason)

  verify : ℕ → (query : Request) → Result (Checked query)
  verify fuel query with R.supported? 0 (Request.subject query)
  ... | no invalid = rejected unsupported-subject
  ... | yes subject-supported with D.infer ⟨⟩ (Request.subject query) (Request.subject-recipe query)
  ... | nothing = rejected inference-failed
  ... | just (inferred , synthesized) with R.supported? 0 inferred
  ... | no invalid = rejected unsupported-inferred
  ... | yes inferred-supported with D.kind ⟨⟩ inferred (Request.inferred-kind-recipe query)
  ... | nothing = rejected inferred-kind-failed
  ... | just (inferred-level , inferred-kind) with R.supported? 0 (Request.goal query)
  ... | no invalid = rejected unsupported-goal
  ... | yes goal-supported with D.kind ⟨⟩ (Request.goal query) (Request.goal-kind-recipe query)
  ... | nothing = rejected goal-kind-failed
  ... | just (goal-level , goal-kind) = choose fuel inferred (λ basis → record
    { subject-supported = subject-supported ; inferred = inferred ; synthesized = synthesized
    ; inferred-supported = inferred-supported ; inferred-level = inferred-level ; inferred-kind = inferred-kind
    ; goal-supported = goal-supported ; goal-level = goal-level ; goal-kind = goal-kind ; basis = basis })
