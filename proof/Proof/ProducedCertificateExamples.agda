{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Literal Elixir producer output, not characters computed by Agda's
-- encoder in the fixture. Exact equality is checked for this artifact.
-- This is not universal Elixir/extraction/kernel-acceptance refinement.
------------------------------------------------------------------------
module Proof.ProducedCertificateExamples where

open import Data.Bool using (true)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Core.Syntax
open import Core.Typing using (⟨⟩)
open import Core.Reduction using (⇝*-step; ⇝*-refl; ι)
import Core.WireCertificate as Codec
import Fixtures.ExecutableCertificate as Produced
import Proof.WireCertificateExamples as Existing
import Proof.NativeCertificateExamples as E
import Proof.ExecutableSnapshotExamples as Input
import Proof.NativeCertificateSafety as Model
import Proof.DependentSoundness as Safety
open import Proof.NativeRecipeExamples using (present)
module Replay = Existing.Replay

same-table : Produced.table ≡ Existing.table
same-table = refl
-- Reduction here compares the literal producer characters with the
-- independently encoded formal payload, including every asserted term.
exact-characters : Produced.characters ≡ Existing.Complete.characters
exact-characters = refl
produced-encoding : Codec.encode Produced.table Existing.payload ≡ just Produced.characters
produced-encoding = refl
produced-decoding : Codec.decode Produced.table Produced.characters ≡ just Existing.payload
produced-decoding = Codec.roundtrip Produced.table Existing.payload Produced.characters produced-encoding

-- Generic transport avoids concrete evidence-value rewriting. Neither
-- the character parser nor native semantic replay is replaced or trusted.
replay-agrees : Replay.checked Produced.table Produced.characters ≡
  Replay.checked Existing.table Existing.Complete.characters
replay-agrees = cong (Replay.checked Produced.table) exact-characters
accepted : present (Replay.checked Produced.table Produced.characters) ≡ true
accepted = trans (cong present replay-agrees) Existing.accepted
certificate : Replay.G.C.Evidence
certificate = Existing.certificate
certificate-from-produced-characters :
  Replay.checked Produced.table Produced.characters ≡ just certificate
certificate-from-produced-characters = trans replay-agrees Existing.certificate-from-characters
valid : E.N.SignatureValid
valid = Replay.G.C.validity certificate
admitted : E.N.Admitted ⟨⟩ E.program tm-atom_type
admitted = Replay.G.C.admitted certificate {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl
eligible : Replay.G.C.A.Eligible ⟨⟩ E.program tm-atom_type
eligible = Replay.G.C.eligible certificate {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl
specification : Safety.Specification E.ind E.sig E.conv
specification = record Model.specification
  { signature-valid = valid
  ; reduction-converts = λ {t} {u} → Input.ConversionModel.reduce-converts {t = t} {u = u}
  ; global-bodies-final = λ {name} → Input.visible-bodies-final {name} }
module Sound = Safety.Sound E.ind E.sig E.conv specification
safe : Sound.SafeState (tm-atom_lit "payload") tm-atom_type
safe = Sound.trace-safe (Replay.G.C.A.Eligible.checked eligible)
  (Replay.G.C.A.Eligible.source-final eligible) (⇝*-step (ι refl refl) ⇝*-refl)
