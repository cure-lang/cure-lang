------------------------------------------------------------------------
-- The second, syntax/payload stage of snapshot replay.
-- Metadata evidence is fixed explicitly: no proof-irrelevance premise.
-- Raw hidden bodies are checked in addition to projected visible ones.
-- This does not check native declaration typing or kernel admission.
------------------------------------------------------------------------
module Core.ExecutableReplay where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Term; Scoped)
open import Core.Signature using (just-inj)
open import Core.Reduction using (Signature)
import Core.CanonicalSnapshot as S
import Core.ExecutableSnapshot as Input
import Core.AdmissionReplay as Syntax
import Proof.Progress as Final

module Replay (source : Input.Input) (metadata : Input.Accepted source) where
  snapshot : S.Snapshot
  snapshot = Input.Accepted.snapshot metadata
  module R = Syntax.Replay snapshot

  record Payloads : Set where
    field
      projected : R.PayloadsSupported
      raw-bodies : All.All (λ entry → R.BodySupported (Input.GlobalInput.body entry))
        (Input.Input.globals source)

  check : Dec Payloads
  check with R.payloads?
  ... | no absent = no (λ payloads → absent (Payloads.projected payloads))
  ... | yes projected with Syntax.all? (λ entry → R.body? (Input.GlobalInput.body entry))
      (Input.Input.globals source)
  ... | no absent = no (λ payloads → absent (Payloads.raw-bodies payloads))
  ... | yes raw = yes record { projected = projected ; raw-bodies = raw }

  present : ∀ {body : Maybe Term} {t}
    → R.BodySupported body → body ≡ just t → R.Supported 0 t
  present {nothing} support ()
  present {just body} support equal with just-inj equal
  ... | refl = support

  raw-body-supported : Payloads → ∀ {entry body}
    → entry ∈ Input.Input.globals source
    → Input.GlobalInput.body entry ≡ just body → R.Supported 0 body
  raw-body-supported payloads member found =
    present (All.lookup (Payloads.raw-bodies payloads) member) found

  raw-body-closed : Payloads → ∀ {entry body}
    → entry ∈ Input.Input.globals source
    → Input.GlobalInput.body entry ≡ just body → Scoped 0 body
  raw-body-closed payloads member found = R.scoped (raw-body-supported payloads member found)

  raw-body-final : Payloads → ∀ {entry body}
    → entry ∈ Input.Input.globals source
    → Input.GlobalInput.body entry ≡ just body → Final.Final body
  raw-body-final payloads member found = R.final (raw-body-supported payloads member found)

  bodies-closed : Payloads → ∀ {name body}
    → Signature.body (S.Snapshot.sig snapshot) name ≡ just body → Scoped 0 body
  bodies-closed payloads {name} = R.bodies-closed (Payloads.projected payloads) {name}

  bodies-final : Payloads → Final.BodiesFinal (S.Snapshot.sig snapshot)
  bodies-final payloads {name} = R.bodies-final (Payloads.projected payloads) {name}

  types-closed : Payloads → ∀ {name T}
    → Signature.type-of (S.Snapshot.sig snapshot) name ≡ just T → Scoped 0 T
  types-closed payloads {name} = R.types-closed (Payloads.projected payloads) {name}
