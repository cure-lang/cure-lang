{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- A checked SYNTACTIC caller frame, not an arbitrary semantic Context.
-- Closed actual terms instantiate a validated forward telescope. Both
-- subject and expected goal are transported by the SAME substitution.
------------------------------------------------------------------------
module Core.CallerAdmission where

open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Core.Syntax
open import Core.Signature using (Telescope)
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; ⟨⟩; Conversion)
open import Core.Reduction using (_⇝*_)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as P
import Core.LocalFrame as F
import Proof.DependentCoherence as Coherence
import Proof.DependentGeneralTransport as General
import Proof.DependentScoping as Scope
import Proof.FinalPreservation as Finality
import Proof.Progress as Final

record Request : Set where
  constructor request
  field
    bindings : Telescope
    kind-recipes : List Recipe
    arguments : List Term
    argument-recipes : List Recipe
    subject goal : Term
    subject-recipe goal-recipe : Recipe

module Replay {source table certificate-chars} (source-checked : P.Checked source table certificate-chars) where
  module C = P.Checked source-checked
  module D = C.W.G.D
  module N = C.W.N
  module R = C.W.R.R
  module Frames = Coherence.NativeFrames C.W.ind C.W.sig C.W.M.conversion
  module Transport = General.General C.W.ind C.W.sig C.W.M.conversion
  module T = Transport.Valid C.valid
  module Sc = Scope.Scoping C.W.ind C.W.sig C.W.M.conversion

  declared-wf : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
    → N.WellFormed Γ → N.Declared Γ tele Δ → N.WellFormed Δ
  declared-wf wf N.dt[] = wf
  declared-wf wf (N.dt∷ scoped kind rest) = declared-wf (N.wf∷ wf scoped kind) rest

  record Checked (query : Request) : Set where
    open Request query
    field
      size : ℕ
      context : Ctx size
      declaration : N.Declared ⟨⟩ bindings context
      supported-declarations : R.TelescopeSupported 0 bindings
      supported-arguments : R.Terms 0 arguments
      actuals : N.Spine ⟨⟩ [] arguments bindings
      supported-subject : R.Supported size subject
      supported-goal : R.Supported size goal
      goal-level : Level
      goal-kind : N._⊢_⇒_ context goal (tm-type goal-level)
      typed : N._⊢_⇒_ context subject goal
    context-valid : N.WellFormed context
    context-valid = declared-wf N.wf[] declaration
    substitution : Sub
    substitution = F.advance arguments F.identity
    arguments-final : Final.FinalTerms arguments
    arguments-final = R.final-terms supported-arguments
    coherent : Frames.Coherent context ⟨⟩ substitution
    coherent = Frames.instantiate-coherent {Γ = ⟨⟩} {Δ = ⟨⟩} {Ε = context}
      {locals = []} {args = arguments} {tele = bindings}
      declaration actuals arguments-final (λ ())
    closed-subject closed-goal : Term
    closed-subject = substS substitution subject
    closed-goal = substS substitution goal
    closed-typed : N._⊢_⇒_ ⟨⟩ closed-subject closed-goal
    closed-typed = T.subst⇒ coherent N.wf[] typed
    closed-kind : N._⊢_⇒_ ⟨⟩ closed-goal (tm-type goal-level)
    closed-kind = T.subst⇒ coherent N.wf[] goal-kind
    admitted : N.Admitted ⟨⟩ closed-subject closed-goal
    admitted = record
      { signature-valid = C.valid ; context-valid = N.wf[]
      ; term-scoped = Sc.infer-scoped closed-typed
      ; goal-scoped = Sc.infer-scoped closed-kind
      ; goal-level = goal-level ; goal-kind = closed-kind
      ; checked = N.⇐-infer closed-typed (Conversion.≈-refl C.W.M.conversion {t = closed-goal}) }
    final : Final.Final closed-subject
    final = subst Final.Final (sym (F.fields-agree arguments subject))
      (Finality.substArgs-final arguments-final (R.final supported-subject))
    trace-safe : ∀ {endpoint} → _⇝*_ C.W.sig closed-subject endpoint
      → C.Sound.SafeState endpoint closed-goal
    trace-safe = C.Sound.trace-safe (N.Admitted.checked admitted) final
    run : ℕ → C.Sound.FuelResult closed-subject closed-goal
    run fuel = C.Sound.soundness-fuel fuel (N.Admitted.checked admitted) final
    tree : C.Sound.EvalTree closed-subject closed-goal
    tree = C.Sound.soundness-tree (N.Admitted.checked admitted) final
    budgets-agree : ∀ fuel → run fuel ≡ C.Sound.truncate fuel tree
    budgets-agree fuel = C.Sound.soundness-fuel≡truncate fuel (N.Admitted.checked admitted) final

  verify : (query : Request) → Maybe (Checked query)
  verify query
    with D.declare ⟨⟩ (Request.bindings query) (Request.kind-recipes query)
  ... | nothing = nothing
  ... | just (size , context , declaration) with R.telescope? 0 (Request.bindings query)
  ... | no rejected = nothing
  ... | yes supported-declarations with R.terms? 0 (Request.arguments query)
  ... | no rejected = nothing
  ... | yes supported-arguments
    with D.spine ⟨⟩ [] (Request.arguments query) (Request.bindings query) (Request.argument-recipes query)
  ... | nothing = nothing
  ... | just actuals with R.supported? size (Request.subject query)
  ... | no rejected = nothing
  ... | yes supported-subject with R.supported? size (Request.goal query)
  ... | no rejected = nothing
  ... | yes supported-goal with D.kind context (Request.goal query) (Request.goal-recipe query)
  ... | nothing = nothing
  ... | just (level , kind) with D.at context (Request.subject query) (Request.goal query) (Request.subject-recipe query)
  ... | nothing = nothing
  ... | just typed = just record
    { size = size ; context = context ; declaration = declaration
    ; supported-declarations = supported-declarations ; supported-arguments = supported-arguments
    ; actuals = actuals ; supported-subject = supported-subject ; supported-goal = supported-goal
    ; goal-level = level ; goal-kind = kind ; typed = typed }
