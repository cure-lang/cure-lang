{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Actual native soundness calls at one fixed Float goal. Endpoint
-- typing is obtained from the theorem, never independently supplied.
------------------------------------------------------------------------
module Proof.DependentSoundnessExamples where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Typing using (⟨⟩)
open import Core.Reduction
open import Proof.Progress using (Final)
import Proof.DependentSoundness as Soundness
import Proof.DependentSoundnessModel as M
open M.N

spec : Soundness.Specification M.env M.sig M.conv
spec = record
  { signature-valid = M.valid
  ; data-components = M.D.data-components
  ; reduction-converts = λ {t} {u} → M.R.reduce-converts {t} {u}
  ; global-bodies-final = λ {f} {body′} → M.bodies-final {f} {body′}
  ; builtin-shapes = M.shapes }
module S = Soundness.Sound M.env M.sig M.conv spec

nat-run : ℕ → S.FuelResult M.program tm-float_type
nat-run fuel = S.soundness-fuel fuel M.program-checked M.program-final
bounded-run : ℕ → S.FuelResult M.bounded-program tm-float_type
bounded-run fuel = S.soundness-fuel fuel M.bounded-checked M.bounded-final

nat-zero-status : S.status (nat-run 0) ≡ S.exhausted-fuel
nat-zero-status = refl
nat-zero-endpoint : S.endpoint (nat-run 0) ≡ M.program
nat-zero-endpoint = refl
nat-three-status : S.status (nat-run 3) ≡ S.exhausted-fuel
nat-three-status = refl
nat-three-endpoint : S.endpoint (nat-run 3) ≡ tm-float_lit
nat-three-endpoint = refl
nat-four-status : S.status (nat-run 4) ≡ S.reached-value
nat-four-status = refl
nat-four-endpoint : S.endpoint (nat-run 4) ≡ tm-float_lit
nat-four-endpoint = refl
bounded-zero-status : S.status (bounded-run 0) ≡ S.exhausted-fuel
bounded-zero-status = refl
bounded-zero-endpoint : S.endpoint (bounded-run 0) ≡ M.bounded-program
bounded-zero-endpoint = refl
bounded-three-status : S.status (bounded-run 3) ≡ S.exhausted-fuel
bounded-three-status = refl
bounded-three-endpoint : S.endpoint (bounded-run 3) ≡ tm-float_lit
bounded-three-endpoint = refl
bounded-four-status : S.status (bounded-run 4) ≡ S.reached-value
bounded-four-status = refl
bounded-four-endpoint : S.endpoint (bounded-run 4) ≡ tm-float_lit
bounded-four-endpoint = refl

-- Status equality eliminates the exhausted branch, retaining exactly
-- the typing, finality, Value and source path returned by soundness.
extract-reached : ∀ {t T} (result : S.FuelResult t T)
  → S.status result ≡ S.reached-value → S.Reached t T
extract-reached (S.reached witness) status = witness
extract-reached (S.exhausted u typed final path) ()
nat-reached : S.Reached M.program tm-float_type
nat-reached = extract-reached (nat-run 4) nat-four-status
bounded-reached : S.Reached M.bounded-program tm-float_type
bounded-reached = extract-reached (bounded-run 4) bounded-four-status

-- Explicit user-supplied relational paths are safe independently of
-- the evaluator's observation policy.
nat-safe : S.SafeState tm-float_lit tm-float_type
nat-safe = S.trace-safe M.program-checked M.program-final M.program-path
bounded-safe : S.SafeState tm-float_lit tm-float_type
bounded-safe = S.trace-safe M.bounded-checked M.bounded-final M.bounded-path
trace-endpoint-typed : ⟨⟩ ⊢ tm-float_lit ⇐ tm-float_type
trace-endpoint-typed = S.SafeState.typed nat-safe
bounded-trace-endpoint-typed : ⟨⟩ ⊢ tm-float_lit ⇐ tm-float_type
bounded-trace-endpoint-typed = S.SafeState.typed bounded-safe
trace-endpoint-final : Final tm-float_lit
trace-endpoint-final = S.SafeState.final nat-safe

nat-tree : S.EvalTree M.program tm-float_type
nat-tree = S.soundness-tree M.program-checked M.program-final
bounded-tree : S.EvalTree M.bounded-program tm-float_type
bounded-tree = S.soundness-tree M.bounded-checked M.bounded-final
nat-tree-source : ⟨⟩ ⊢ M.program ⇐ tm-float_type
nat-tree-source = S.EvalTree.typed nat-tree
bounded-tree-source : ⟨⟩ ⊢ M.bounded-program ⇐ tm-float_type
bounded-tree-source = S.EvalTree.typed bounded-tree
nat-tree-agreement : ∀ fuel → nat-run fuel ≡ S.truncate fuel nat-tree
nat-tree-agreement fuel = S.soundness-fuel≡truncate fuel M.program-checked M.program-final
bounded-tree-agreement : ∀ fuel → bounded-run fuel ≡ S.truncate fuel bounded-tree
bounded-tree-agreement fuel = S.soundness-fuel≡truncate fuel M.bounded-checked M.bounded-final
nat-tree-three-status : S.status (S.truncate 3 nat-tree) ≡ S.exhausted-fuel
nat-tree-three-status = refl
nat-tree-three-endpoint : S.endpoint (S.truncate 3 nat-tree) ≡ tm-float_lit
nat-tree-three-endpoint = refl
nat-tree-four-status : S.status (S.truncate 4 nat-tree) ≡ S.reached-value
nat-tree-four-status = refl
nat-tree-four-endpoint : S.endpoint (S.truncate 4 nat-tree) ≡ tm-float_lit
nat-tree-four-endpoint = refl
bounded-tree-three-status : S.status (S.truncate 3 bounded-tree) ≡ S.exhausted-fuel
bounded-tree-three-status = refl
bounded-tree-three-endpoint : S.endpoint (S.truncate 3 bounded-tree) ≡ tm-float_lit
bounded-tree-three-endpoint = refl
bounded-tree-four-status : S.status (S.truncate 4 bounded-tree) ≡ S.reached-value
bounded-tree-four-status = refl
bounded-tree-four-endpoint : S.endpoint (S.truncate 4 bounded-tree) ≡ tm-float_lit
bounded-tree-four-endpoint = refl

-- Zero fuel does not inspect the current endpoint. Exhaustion is
-- therefore compatible with an already reached Value, not divergence.
nat-exhausted-at-value :
  S.status (nat-run 3) ≡ S.exhausted-fuel × Value (S.endpoint (nat-run 3))
nat-exhausted-at-value = refl , canonical c-float_lit
bounded-exhausted-at-value :
  S.status (bounded-run 3) ≡ S.exhausted-fuel × Value (S.endpoint (bounded-run 3))
bounded-exhausted-at-value = refl , canonical c-float_lit
float-no-step : ∀ {u} → _⇝_ M.sig tm-float_lit u → ⊥
float-no-step ()
float-not-diverging : S.Diverges tm-float_lit → ⊥
float-not-diverging path with S.Diverges.step path
... | u , step , rest = float-no-step step
exhaustion-not-divergence :
  (∀ {t T} (result : S.FuelResult t T)
    → S.status result ≡ S.exhausted-fuel
    → S.Diverges (S.endpoint result)) → ⊥
exhaustion-not-divergence claim = float-not-diverging (claim (nat-run 3) refl)
