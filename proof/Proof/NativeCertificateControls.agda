------------------------------------------------------------------------
-- Representation replay is not native declaration/body certification.
-- Negative inversions are checked under an abstract conversion parameter.
------------------------------------------------------------------------
module Proof.NativeCertificateControls where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature
open import Core.Coverage
open import Core.TypeHeads
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; ⟨⟩; Conversion)
open import Core.Universe using (l0; l2)
import Core.DependentTyping as Native
import Core.ExecutableSnapshot as Input
import Core.ExecutableReplay as Replay
import Core.NativeCertificate as Certificate
import Core.CanonicalSnapshot as S
import Proof.ReductionConversion as Reduction
import Proof.DependentTypingInversion as Inversion
import Proof.NativeCertificateExamples as E
import Proof.ExecutableSnapshotExamples as FixtureEvidence
import Fixtures.ExecutableSnapshot as Fixture

module Refute (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  module N = Native.Typing ind sig conv
  module I = Inversion.Laws ind sig conv
  abstract
    type2-no-inference : ∀ {n} {Γ : Ctx n} {T} → N._⊢_⇒_ Γ (tm-type l2) T → ⊥
    type2-no-inference (N.⇒-type ())
    type2-no-inference (N.⇒-conv typed equal) = type2-no-inference typed
    type2-no-inference (N.⇒-cumul typed le) = type2-no-inference typed

    bad-declaration : ∀ {m} {Δ : Ctx m}
      → N.Declared ⟨⟩ (("bad" , tm-type l2) ∷ []) Δ → ⊥
    bad-declaration (N.dt∷ scope kind rest) = type2-no-inference kind

    atom-not-float : ∀ {name} → N._⊢_⇒_ ⟨⟩ (tm-atom_lit name) tm-float_type → ⊥
    atom-not-float typed with Conversion.≈-heads conv
      {t = tm-atom_type} {u = tm-float_type} ty-atom ty-float (I.atom-inference typed)
    ... | ()

-- This whole input passes metadata and complete syntax replay, yet no
-- finite native evidence can supply its published type's kind.
bad-kind-entry : Input.GlobalInput
bad-kind-entry = record FixtureEvidence.raw-answer { type = tm-type l2 }
bad-kind-source : Input.Input
bad-kind-source = record Fixture.source { globals = bad-kind-entry ∷ [] }
bad-kind-metadata : Input.Accepted bad-kind-source
bad-kind-metadata = FixtureEvidence.witness (Input.check bad-kind-source) refl
module KindReplay = Replay.Replay bad-kind-source bad-kind-metadata
kind-payloads : KindReplay.Payloads
kind-payloads = FixtureEvidence.witness KindReplay.check refl
module KindConversion = Reduction.Model (S.Snapshot.sig KindReplay.snapshot)
  (λ {name} → KindReplay.bodies-closed kind-payloads {name})
module KindCertificate = Certificate.Certificates bad-kind-source bad-kind-metadata
  kind-payloads KindConversion.conversion
module K = Refute (S.Snapshot.ind KindReplay.snapshot) (S.Snapshot.sig KindReplay.snapshot)
  KindConversion.conversion
bad-kind-certificate : KindCertificate.Evidence → ⊥
bad-kind-certificate evidence = K.type2-no-inference
  (KindCertificate.GlobalEvidence.kind (All.lookup (KindCertificate.Evidence.definitions evidence) (here refl)))

-- The bad body is HIDDEN. Native evidence is required for raw definitions,
-- not just the visible global table.
bad-body-entry : Input.GlobalInput
bad-body-entry = record FixtureEvidence.raw-held { type = tm-float_type }
bad-body-source : Input.Input
bad-body-source = record Fixture.source { globals = bad-body-entry ∷ [] }
bad-body-metadata : Input.Accepted bad-body-source
bad-body-metadata = FixtureEvidence.witness (Input.check bad-body-source) refl
module BodyReplay = Replay.Replay bad-body-source bad-body-metadata
body-payloads : BodyReplay.Payloads
body-payloads = FixtureEvidence.witness BodyReplay.check refl
module BodyConversion = Reduction.Model (S.Snapshot.sig BodyReplay.snapshot)
  (λ {name} → BodyReplay.bodies-closed body-payloads {name})
module BodyCertificate = Certificate.Certificates bad-body-source bad-body-metadata
  body-payloads BodyConversion.conversion
module B = Refute (S.Snapshot.ind BodyReplay.snapshot) (S.Snapshot.sig BodyReplay.snapshot)
  BodyConversion.conversion
bad-hidden-body-certificate : BodyCertificate.Evidence → ⊥
bad-hidden-body-certificate evidence = B.atom-not-float
  (BodyCertificate.GlobalEvidence.body (All.lookup (BodyCertificate.Evidence.definitions evidence) (here refl)))

module N = E.N
abstract
  missing-fields : ∀ {T} → N._⊢_⇒_ ⟨⟩ (tm-ctor "Boundary#Pack" []) T → ⊥
  missing-fields (N.⇒-ctor found params args) with just-inj found
  ... | refl with args
  ... | ()
  missing-fields (N.⇒-conv typed equal) = missing-fields typed
  missing-fields (N.⇒-cumul typed le) = missing-fields typed

  missing-alternative-coverage :
    CaseCoverage E.ind "Boundary#Packed" (("Boundary#Pack" , 2 , tm-var 0) ∷ []) → ⊥
  missing-alternative-coverage covered
    with ctor-covered covered {c = "Boundary#Alternate"} refl refl
  ... | body , ()

  too-small-field-budget : N.LevelsBelow l0 E.fields-declared → ⊥
  too-small-field-budget (() , rest)

-- Finite evidence must include the actual second constructor, even though
-- only the first one is selected by the exported ordinary-case fixture.
second-constructor-required : E.C.Evidence → N.ConstructorDeclaration E.family E.alternate
second-constructor-required evidence =
  All.lookup
    (E.C.FamilyEvidence.constructors (All.lookup (E.C.Evidence.families evidence) (here refl)))
    (there (here refl))
