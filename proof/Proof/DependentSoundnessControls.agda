{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- An intentionally recursive SPECIFICATION table, not an executable
-- totality certificate. BodiesFinal does not imply termination.
-- Positive divergence can coexist with Value and zero-step Reached.
------------------------------------------------------------------------
module Proof.DependentSoundnessControls where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Data.Nat using (ℕ; zero; suc)
open import Core.Syntax
open import Core.Signature
open import Core.Universe using (l0)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Reduction
import Core.DependentTyping as Native
open import Proof.Progress using (BodiesFinal; Final; f-global)
import Proof.ReductionConversion as Reduction
import Proof.DependentDataConversion as Data
import Proof.DependentLiteralPreservation as Literal
import Proof.DependentSoundness as Soundness

env : IndEnv
env = record { families = [] ; builtins = λ _ → nothing }
loop : Term
loop = tm-global "loop"
types bodies : Name → Maybe Term
types name with name ≟ "loop"
... | yes equal = just tm-float_type
... | no different with name ≟ "opaque"
... | yes equal = just tm-float_type
... | no other = nothing
bodies name with name ≟ "loop"
... | yes equal = just loop
... | no different = nothing
sig : Signature
sig = record { type-of = types ; body = bodies }

body-closed : ∀ {name b} → bodies name ≡ just b → Scoped 0 b
body-closed {name} found with name ≟ "loop"
... | yes equal with just-inj found
... | refl = sc-global
body-closed {name} () | no different
module R = Reduction.Model sig body-closed
conv : Conversion
conv = R.conversion
module D = Data.Model sig body-closed
module T = Native.Typing env sig conv
open T

type-valid : ∀ {name A} → types name ≡ just A
  → Scoped 0 A × (Data.Product.∃ λ level → ⟨⟩ ⊢ A ⇒ tm-type level)
type-valid {name} found with name ≟ "loop"
... | yes equal with just-inj found
... | refl = sc-float_type , l0 , ⇒-float_type
type-valid {name} found | no different with name ≟ "opaque"
... | yes equal with just-inj found
... | refl = sc-float_type , l0 , ⇒-float_type
type-valid {name} () | no different | no other
body-valid : ∀ {name b} → bodies name ≡ just b
  → Data.Product.∃ λ A → types name ≡ just A × Scoped 0 b × (⟨⟩ ⊢ b ⇒ A)
body-valid {name} found with name ≟ "loop"
... | yes refl with just-inj found
... | refl = tm-float_type , refl , sc-global , ⇒-global refl
body-valid {name} () | no different
valid : SignatureValid
valid = record
  { family-declared = λ () ; constructor-declared = λ () ; owner-visible = λ ()
  ; global-type = λ {name} → type-valid {name}
  ; global-body = λ {name} → body-valid {name} }
bodies-final : BodiesFinal sig
bodies-final {f} found with f ≟ "loop"
... | yes equal with just-inj found
... | refl = f-global
bodies-final {f} () | no different
spec : Soundness.Specification env sig conv
spec = record
  { signature-valid = valid ; data-components = D.data-components
  ; reduction-converts = R.reduce-converts ; global-bodies-final = bodies-final
  ; builtin-shapes = Literal.no-builtins env (λ _ → refl) }
module S = Soundness.Sound env sig conv spec

source : ⟨⟩ ⊢ loop ⇐ tm-float_type
source = ⇐-infer (⇒-global refl) (Conversion.≈-refl conv {t = tm-float_type})
loop-step : _⇝_ sig loop loop
loop-step = δ refl
loop-diverges : S.Diverges loop
S.Diverges.step loop-diverges = loop , loop-step , loop-diverges
typed-loop-diverges : S.TypedDiverges loop tm-float_type
typed-loop-diverges = S.annotate-divergence source f-global loop-diverges
loop-tree : S.EvalTree loop tm-float_type
loop-tree = S.soundness-tree source f-global

status-prefix : ∀ {t u A} (step : _⇝_ sig t u) (result : S.FuelResult u A)
  → S.status (S.prepend-step step result) ≡ S.status result
status-prefix step (S.reached witness) = refl
status-prefix step (S.exhausted u typed final path) = refl
endpoint-prefix : ∀ {t u A} (step : _⇝_ sig t u) (result : S.FuelResult u A)
  → S.endpoint (S.prepend-step step result) ≡ S.endpoint result
endpoint-prefix step (S.reached witness) = refl
endpoint-prefix step (S.exhausted u typed final path) = refl

-- Generalize over source proof objects: recursively produced typings
-- need not be definitionally the same proof as the initial one.
loop-exhausts : ∀ fuel (typed : ⟨⟩ ⊢ loop ⇐ tm-float_type) (final : Final loop)
  → S.status (S.soundness-fuel fuel typed final) ≡ S.exhausted-fuel
loop-exhausts zero typed final = refl
loop-exhausts (suc fuel) typed final =
  trans (status-prefix loop-step
    (S.soundness-fuel fuel (S.next-typed typed final loop-step) (S.next-final final loop-step)))
    (loop-exhausts fuel (S.next-typed typed final loop-step) (S.next-final final loop-step))
loop-endpoint : ∀ fuel (typed : ⟨⟩ ⊢ loop ⇐ tm-float_type) (final : Final loop)
  → S.endpoint (S.soundness-fuel fuel typed final) ≡ loop
loop-endpoint zero typed final = refl
loop-endpoint (suc fuel) typed final =
  trans (endpoint-prefix loop-step
    (S.soundness-fuel fuel (S.next-typed typed final loop-step) (S.next-final final loop-step)))
    (loop-endpoint fuel (S.next-typed typed final loop-step) (S.next-final final loop-step))

-- Value includes neutrals, even a defined global that can unfold.
loop-value : Value loop
loop-value = neutral n-global
loop-reached : S.Reached loop tm-float_type
loop-reached = loop , source , f-global , loop-value , ⇝*-refl
divergence-does-not-exclude-reached : S.Diverges loop × S.Reached loop tm-float_type
divergence-does-not-exclude-reached = loop-diverges , loop-reached
no-reachable-value-claim-refuted :
  (S.Diverges loop → ∀ v → _⇝*_ sig loop v → Value v → ⊥) → ⊥
no-reachable-value-claim-refuted impossible =
  impossible loop-diverges loop ⇝*-refl loop-value

opaque-source : ⟨⟩ ⊢ tm-global "opaque" ⇐ tm-float_type
opaque-source = ⇐-infer (⇒-global refl) (Conversion.≈-refl conv {t = tm-float_type})
opaque-reaches : S.status (S.soundness-fuel 1 opaque-source f-global) ≡ S.reached-value
opaque-reaches = refl
