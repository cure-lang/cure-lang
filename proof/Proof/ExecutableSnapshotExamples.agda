------------------------------------------------------------------------
-- Replay the EXACT generated data tested by the executable exporter.
-- This is concrete artifact agreement, not universal extraction or
-- algorithmic admission soundness; metadata flags are still only claims.
------------------------------------------------------------------------
module Proof.ExecutableSnapshotExamples where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
import Data.List as List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Core.Syntax
open import Core.Signature
open import Core.Grade using (unrestricted; erased)
open import Core.Universe using (l0)
open import Core.Reduction using (Signature)
open import Core.ExecutableSnapshot
import Core.CanonicalSnapshot as S
import Core.ExecutableReplay as Complete
import Proof.Progress as Final
import Proof.ReductionConversion as Reduction
import Fixtures.ExecutableSnapshot as Fixture

decision : ∀ {A : Set} → Dec A → Bool
decision (yes proof) = true
decision (no refute) = false
witness : ∀ {A : Set} (checked : Dec A) → decision checked ≡ true → A
witness (yes proof) accepted = proof
witness (no refute) ()

accepted : Accepted Fixture.source
accepted = witness (check Fixture.source) refl
snapshot : S.Snapshot
snapshot = Accepted.snapshot accepted
module CompleteReplay = Complete.Replay Fixture.source accepted
module B = CompleteReplay.R.B
open B

replayed : CompleteReplay.Payloads
replayed = witness CompleteReplay.check refl

raw-family : FamilyInput
raw-family = List.lookup (Input.families Fixture.source) Fin.zero
raw-ctor : ConstructorInput
raw-ctor = List.lookup (FamilyInput.constructors raw-family) Fin.zero
raw-answer raw-held raw-packed raw-unpack : GlobalInput
raw-answer = List.lookup (Input.globals Fixture.source) Fin.zero
raw-held = List.lookup (Input.globals Fixture.source) (Fin.suc Fin.zero)
raw-packed = List.lookup (Input.globals Fixture.source) (Fin.suc (Fin.suc Fin.zero))
raw-unpack = List.lookup (Input.globals Fixture.source) (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
packed : Family
packed = project-family raw-family
pack : Ctor
pack = ConstructorInput.declaration raw-ctor

family-lookup : findFamily "Boundary#Packed" (S.Snapshot.family-entries snapshot) ≡ just packed
family-lookup = sym (S.family-lookup-agrees "Boundary#Packed" (S.Snapshot.family-entries snapshot))
ctor-lookup : findCtor "Boundary#Pack" (S.Snapshot.family-entries snapshot) ≡ just (packed , pack)
ctor-lookup = sym (S.constructor-lookup-agrees "Boundary#Pack" (S.Snapshot.family-entries snapshot))
owner-lookup : findFamily (fam-name packed) (S.Snapshot.family-entries snapshot) ≡ just packed
owner-lookup = S.Snapshot.owner-visible snapshot {name = "Boundary#Pack"} ctor-lookup
unproved-positivity : positive packed ≡ false
unproved-positivity = refl
unproved-universe-certificate : universe-ok packed ≡ false
unproved-universe-certificate = refl

answer-visible : Signature.body (S.Snapshot.sig snapshot) "Boundary#answer"
  ≡ just (tm-atom_lit "answer")
answer-visible = refl
hidden-type-present : Signature.type-of (S.Snapshot.sig snapshot) "Boundary#held" ≡ just tm-atom_type
hidden-type-present = refl
hidden-body-absent : Signature.body (S.Snapshot.sig snapshot) "Boundary#held" ≡ nothing
hidden-body-absent = refl
hidden-raw-body-retained : GlobalInput.body raw-held ≡ just (tm-atom_lit "hidden")
hidden-raw-body-retained = refl

goal-supported : ∀ {n} → Supported n (tm-data "Boundary#Packed" [] (tm-atom_type ∷ []))
goal-supported {n} = witness
  (CompleteReplay.R.supported? n (tm-data "Boundary#Packed" [] (tm-atom_type ∷ []))) refl
value-supported : Supported 0
  (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ []))
value-supported = witness
  (CompleteReplay.R.supported? 0
    (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ []))) refl
motive-supported : Supported 0
  (tm-lam unrestricted (tm-type l0)
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1)))
motive-supported = witness
  (CompleteReplay.R.supported? 0
    (tm-lam unrestricted (tm-type l0)
      (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1)))) refl
raw-program-supported : BodySupported (GlobalInput.body raw-unpack)
raw-program-supported = CompleteReplay.raw-body-supported replayed {entry = raw-unpack}
  (there (there (there (here refl)))) refl

-- Projected payloads are supported, with independent support above for
-- the hidden raw dependent program. No native typing is inferred here.
payloads : PayloadsSupported
payloads = CompleteReplay.Payloads.projected replayed

visible-bodies-closed : ∀ {name b}
  → Signature.body (S.Snapshot.sig snapshot) name ≡ just b → Scoped 0 b
visible-bodies-closed {name} = CompleteReplay.bodies-closed replayed {name}
visible-bodies-final : Final.BodiesFinal (S.Snapshot.sig snapshot)
visible-bodies-final {name} = CompleteReplay.bodies-final replayed {name}
declared-goal-closed : Scoped 0 (tm-data "Boundary#Packed" [] (tm-atom_type ∷ []))
declared-goal-closed = CompleteReplay.types-closed replayed {name = "Boundary#packed"} refl
hidden-program-final : Final.Final
  (tm-case (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ []))
    (tm-lam unrestricted (tm-type l0)
      (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1)))
    (("Boundary#Pack" , 2 , tm-var 0) ∷ ("Boundary#Alternate" , 2 , tm-var 0) ∷ []))
hidden-program-final = CompleteReplay.raw-body-final replayed {entry = raw-unpack}
  (there (there (there (here refl)))) refl

-- The reduction model now consumes a derived finite-payload invariant,
-- rather than a fixture-specific closed-body callback.
module ConversionModel = Reduction.Model (S.Snapshot.sig snapshot)
  (λ {name} → visible-bodies-closed {name})
answer-converts : ConversionModel._≈_ (tm-global "Boundary#answer") (tm-atom_lit "answer")
answer-converts = ConversionModel.reduce-converts
  {t = tm-global "Boundary#answer"} {u = tm-atom_lit "answer"} (Core.Reduction.δ refl)

duplicate-families : Input
duplicate-families = record Fixture.source { families = raw-family ∷ raw-family ∷ [] }
duplicate-rejected : decision (check duplicate-families) ≡ false
duplicate-rejected = refl

duplicate-constructors : Input
duplicate-constructors = record Fixture.source
  { families = record raw-family { constructors = raw-ctor ∷ raw-ctor ∷ [] } ∷ [] }
duplicate-constructors-rejected : decision (check duplicate-constructors) ≡ false
duplicate-constructors-rejected = refl

duplicate-globals : Input
duplicate-globals = record Fixture.source { globals = raw-answer ∷ raw-answer ∷ [] }
duplicate-globals-rejected : decision (check duplicate-globals) ≡ false
duplicate-globals-rejected = refl

opaque-family : Input
opaque-family = record Fixture.source
  { families = record raw-family { is-opaque = true } ∷ [] }
opaque-rejected : decision (check opaque-family) ≡ false
opaque-rejected = refl

erased-fields : Input
erased-fields = record Fixture.source
  { families = record raw-family
      { constructors = record raw-ctor { quantities = erased ∷ unrestricted ∷ [] } ∷ [] } ∷ [] }
erased-rejected : decision (check erased-fields) ≡ false
erased-rejected = refl

missing-layout-slots : Input
missing-layout-slots = record Fixture.source
  { families = record raw-family
      { constructors = record raw-ctor { explicit = [] } ∷ [] } ∷ [] }
missing-layout-rejected : decision (check missing-layout-slots) ≡ false
missing-layout-rejected = refl

implicit-field : Input
implicit-field = record Fixture.source
  { families = record raw-family
      { constructors = record raw-ctor { explicit = false ∷ true ∷ [] } ∷ [] } ∷ [] }
implicit-field-rejected : decision (check implicit-field) ≡ false
implicit-field-rejected = refl

missing-certified-body : Input
missing-certified-body = record Fixture.source
  { globals = record raw-answer { body = nothing } ∷ [] }
missing-body-rejected : decision (check missing-certified-body) ≡ false
missing-body-rejected = refl

unbacked-visibility : Input
unbacked-visibility = record Fixture.source
  { globals = record raw-answer { totality-certified = false } ∷ [] }
unbacked-rejected : decision (check unbacked-visibility) ≡ false
unbacked-rejected = refl

builtin-registration : Input
builtin-registration = record Fixture.source { builtins = ("any" , "Boundary#Packed") ∷ [] }
builtin-rejected : decision (check builtin-registration) ≡ false
builtin-rejected = refl

-- Totality metadata is not body visibility.
total-only : GlobalInput
total-only = record raw-answer { certified = false }
total-only-hidden : S.visible-body (project-global total-only) ≡ nothing
total-only-hidden = uncertified-hidden total-only refl
