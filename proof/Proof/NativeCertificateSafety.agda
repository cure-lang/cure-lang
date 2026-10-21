{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Native specification safety instantiated from finite certificates on
-- the actual exported snapshot. NOT evaluator/Elixir/BEAM refinement.
------------------------------------------------------------------------
module Proof.NativeCertificateSafety where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Reduction
open import Core.Typing using (⟨⟩; Conversion)
import Proof.Progress as Final
import Proof.DependentSoundness as Safety
import Proof.DependentDataConversion as Components
import Proof.DependentLiteralPreservation as Layouts
import Proof.ExecutableSnapshotExamples as Replay
import Proof.NativeCertificateExamples as E
open E.N

module D = Components.Model E.sig (λ {name} → Replay.visible-bodies-closed {name})
specification : Safety.Specification E.ind E.sig E.conv
specification = record
  { signature-valid = E.C.validity E.evidence
  ; data-components = D.data-components
  ; reduction-converts = λ {t} {u} → Replay.ConversionModel.reduce-converts {t = t} {u = u}
  ; global-bodies-final = λ {name} → Replay.visible-bodies-final {name}
  ; builtin-shapes = Layouts.no-builtins E.ind (λ key → refl) }
module Sound = Safety.Sound E.ind E.sig E.conv specification

source-typed : ⟨⟩ ⊢ E.program ⇐ tm-atom_type
source-typed = E.C.A.Eligible.checked E.program-eligible
source-final : Final.Final E.program
source-final = E.C.A.Eligible.source-final E.program-eligible
source-step : _⇝_ E.sig E.program (tm-atom_lit "payload")
source-step = ι refl refl
endpoint-safe : Sound.SafeState (tm-atom_lit "payload") tm-atom_type
endpoint-safe = Sound.trace-safe source-typed source-final (⇝*-step source-step ⇝*-refl)

run : (fuel : ℕ) → Sound.FuelResult E.program tm-atom_type
run fuel = Sound.soundness-fuel fuel source-typed source-final
zero-exhausted : Sound.status (run 0) ≡ Sound.exhausted-fuel
zero-exhausted = refl
one-exhausted-at-value : Sound.status (run 1) ≡ Sound.exhausted-fuel
one-exhausted-at-value = refl
one-endpoint : Sound.endpoint (run 1) ≡ tm-atom_lit "payload"
one-endpoint = refl
two-reached : Sound.status (run 2) ≡ Sound.reached-value
two-reached = refl
two-endpoint : Sound.endpoint (run 2) ≡ tm-atom_lit "payload"
two-endpoint = refl
tree : Sound.EvalTree E.program tm-atom_type
tree = Sound.soundness-tree source-typed source-final
budgets-agree : ∀ fuel → run fuel ≡ Sound.truncate fuel tree
budgets-agree fuel = Sound.soundness-fuel≡truncate fuel source-typed source-final

-- Both source and endpoint goals are Atom even though the alternative
-- constructor's result index computes before conversion.
computed-typed : ⟨⟩ ⊢ E.computed-program ⇐ tm-atom_type
computed-typed = E.check E.computed-program-typed
computed-final : Final.Final E.computed-program
computed-final = Replay.B.final
  (Replay.witness (Replay.CompleteReplay.R.supported? 0 E.computed-program) refl)
computed-step : _⇝_ E.sig E.computed-program (tm-atom_lit "payload")
computed-step = ι refl refl
computed-safe : Sound.SafeState (tm-atom_lit "payload") tm-atom_type
computed-safe = Sound.trace-safe computed-typed computed-final (⇝*-step computed-step ⇝*-refl)

-- A supplied certified-global delta trace, independently of the chosen
-- observation policy; the endpoint's typing comes from native safety.
global-typed : ⟨⟩ ⊢ tm-global "Boundary#answer" ⇐ tm-atom_type
global-typed = E.check (⇒-global refl)
global-step : _⇝_ E.sig (tm-global "Boundary#answer") (tm-atom_lit "answer")
global-step = δ refl
global-safe : Sound.SafeState (tm-atom_lit "answer") tm-atom_type
global-safe = Sound.trace-safe global-typed Final.f-global (⇝*-step global-step ⇝*-refl)
