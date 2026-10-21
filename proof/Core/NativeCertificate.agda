------------------------------------------------------------------------
-- Finite native proof certificates, NOT an algorithmic type checker.
-- No SignatureValid, lookup-typing or preservation callback is a field.
-- All raw definitions, including hidden ones, carry native body proofs.
------------------------------------------------------------------------
module Core.NativeCertificate where

open import Data.Empty using (⊥-elim)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Coverage using (lookup-ctor-members)
open import Core.ClosedFragment using (family-lookup-member)
open import Core.Reduction using (Signature)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Universe using (Level)
import Core.DependentTyping as Native
import Core.CanonicalSnapshot as S
import Core.ExecutableSnapshot as I
import Core.ExecutableReplay as Replay

-- Invert/construct membership of the ACTUAL projected global table.
global-member : ∀ {xs key entry}
  → (key , entry) ∈ I.global-entries (I.input [] xs [])
  → ∃ λ raw → raw ∈ xs × key ≡ I.GlobalInput.name raw × entry ≡ I.project-global raw
global-member {xs = raw ∷ rest} (here refl) = raw , here refl , refl , refl
global-member {xs = raw ∷ rest} (there member) with global-member {xs = rest} member
... | found , member , key , entry = found , there member , key , entry

project-member : ∀ {xs raw} → raw ∈ xs
  → (I.GlobalInput.name raw , I.project-global raw) ∈ I.global-entries (I.input [] xs [])
project-member (here refl) = here refl
project-member (there member) = there (project-member member)

module Certificates (source : I.Input) (metadata : I.Accepted source)
  (payloads : Replay.Replay.Payloads source metadata) (conv : Conversion) where
  module R = Replay.Replay source metadata
  open S.Snapshot R.snapshot using (family-entries; globals; ind; sig; global-keys)
  module N = Native.Typing ind sig conv

  record FamilyEvidence (family : Family) : Set where
    field
      declaration : N.FamilyDeclaration family
      constructors : All.All (N.ConstructorDeclaration family) (fam-ctors family)

  BodyTyped : Term → Maybe Term → Set
  BodyTyped goal nothing = ⊤
  BodyTyped goal (just body) = N._⊢_⇒_ ⟨⟩ body goal

  record GlobalEvidence (entry : I.GlobalInput) : Set where
    field
      level : Level
      kind : N._⊢_⇒_ ⟨⟩ (I.GlobalInput.type entry) (tm-type level)
      body : BodyTyped (I.GlobalInput.type entry) (I.GlobalInput.body entry)

  record Evidence : Set where
    field
      families : All.All FamilyEvidence family-entries
      definitions : All.All GlobalEvidence (I.Input.globals source)

  family-declared : Evidence → ∀ {name family}
    → findFamily name family-entries ≡ just family → N.FamilyDeclaration family
  family-declared evidence {name} found =
    FamilyEvidence.declaration (All.lookup (Evidence.families evidence)
      (family-lookup-member {name = name} {fs = family-entries} found))

  constructor-declared : Evidence → ∀ {name family ctor}
    → findCtor name family-entries ≡ just (family , ctor) → N.ConstructorDeclaration family ctor
  constructor-declared evidence {name} found with lookup-ctor-members {c = name} {fs = family-entries} found
  ... | family-member , ctor-member , equal =
    All.lookup (FamilyEvidence.constructors (All.lookup (Evidence.families evidence) family-member)) ctor-member

  selected-type : ∀ {name entry} → S.lookup name globals ≡ just entry
    → Signature.type-of sig name ≡ just (S.declared-type entry)
  selected-type {name} = S.global-type-found {globals = globals} {key = name}

  raw-infer : ∀ {entry b} → GlobalEvidence entry
    → I.GlobalInput.body entry ≡ just b → N._⊢_⇒_ ⟨⟩ b (I.GlobalInput.type entry)
  raw-infer {I.global-input name ty nothing qs ps certified total} evidence ()
  raw-infer {I.global-input name ty (just body) qs ps certified total} evidence found with just-inj found
  ... | refl = GlobalEvidence.body evidence

  visible-raw : ∀ {entry b} → S.visible-body (I.project-global entry) ≡ just b
    → I.GlobalInput.body entry ≡ just b
  visible-raw {I.global-input name ty body qs ps false total} ()
  visible-raw {I.global-input name ty body qs ps true total} found = found

  global-type : Evidence → ∀ {name T} → Signature.type-of sig name ≡ just T
    → Scoped 0 T × (∃ λ level → N._⊢_⇒_ ⟨⟩ T (tm-type level))
  global-type evidence {name} found with S.lookup name globals in selected
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just entry with global-member {xs = I.Input.globals source}
      (S.lookup-member {key = name} {table = globals} selected)
  ... | raw , member , refl , refl with just-inj found
  ... | refl =
    R.types-closed payloads {name = I.GlobalInput.name raw} (selected-type selected) ,
    GlobalEvidence.level (All.lookup (Evidence.definitions evidence) member) ,
    GlobalEvidence.kind (All.lookup (Evidence.definitions evidence) member)

  global-body : Evidence → ∀ {name b} → Signature.body sig name ≡ just b
    → ∃ λ T → Signature.type-of sig name ≡ just T × Scoped 0 b × N._⊢_⇒_ ⟨⟩ b T
  global-body evidence {name} found with S.lookup name globals in selected
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just entry with global-member {xs = I.Input.globals source}
      (S.lookup-member {key = name} {table = globals} selected)
  ... | raw , member , refl , refl =
    I.GlobalInput.type raw , refl ,
    R.raw-body-closed payloads member (visible-raw {entry = raw} found) ,
    raw-infer (All.lookup (Evidence.definitions evidence) member) (visible-raw {entry = raw} found)

  validity : Evidence → N.SignatureValid
  validity evidence = record
    { family-declared = λ {name} → family-declared evidence {name}
    ; constructor-declared = λ {name} → constructor-declared evidence {name}
    ; owner-visible = λ {name} → S.Snapshot.owner-visible R.snapshot {name = name}
    ; global-type = λ {name} → global-type evidence {name}
    ; global-body = λ {name} → global-body evidence {name} }

  raw-found : ∀ {entry} → entry ∈ I.Input.globals source
    → S.lookup (I.GlobalInput.name entry) globals ≡ just (I.project-global entry)
  raw-found member = S.member-lookup global-keys (project-member member)

  admitted : Evidence → ∀ {entry b}
    → entry ∈ I.Input.globals source → I.GlobalInput.body entry ≡ just b
    → N.Admitted ⟨⟩ b (I.GlobalInput.type entry)
  admitted evidence {entry} member found = record
    { signature-valid = validity evidence ; context-valid = N.wf[]
    ; term-scoped = R.raw-body-closed payloads member found
    ; goal-scoped = R.types-closed payloads {name = I.GlobalInput.name entry} (selected-type (raw-found member))
    ; goal-level = GlobalEvidence.level (All.lookup (Evidence.definitions evidence) member)
    ; goal-kind = GlobalEvidence.kind (All.lookup (Evidence.definitions evidence) member)
    ; checked = N.⇐-infer (raw-infer (All.lookup (Evidence.definitions evidence) member) found)
        (Conversion.≈-refl conv {t = I.GlobalInput.type entry}) }

  module A = R.R.Admission conv
  eligible : Evidence → ∀ {entry b}
    → entry ∈ I.Input.globals source → I.GlobalInput.body entry ≡ just b
    → A.Eligible ⟨⟩ b (I.GlobalInput.type entry)
  eligible evidence {entry} member found = record
    { payloads = R.Payloads.projected payloads ; caller = λ ()
    ; source = R.raw-body-supported payloads member found
    ; goal = R.R.type-supported (R.Payloads.projected payloads)
        {name = I.GlobalInput.name entry} (selected-type (raw-found member))
    ; native = admitted evidence member found }
