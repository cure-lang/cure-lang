------------------------------------------------------------------------
-- Table algebra controls, including the distinction between defined
-- first-match lookup and a unique-key snapshot suitable for a map view.
------------------------------------------------------------------------
module Proof.CanonicalSnapshotExamples where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
import Core.CanonicalSnapshot as S
import Proof.AdmissionBoundaryExamples as E

second : Family
second = record E.family { fam-name = "Other#Packed" }

first-owner-wins : S.lookup "Boundary#Pack"
  (S.constructorTable (E.family ∷ second ∷ [])) ≡ just (E.family , E.ctor)
first-owner-wins = refl
reverse-owner-wins : S.lookup "Boundary#Pack"
  (S.constructorTable (second ∷ E.family ∷ [])) ≡ just (second , E.ctor)
reverse-owner-wins = refl
-- The derived lookup theorem does NOT pretend conflicting ownership
-- becomes order independent, even when the table is malformed.
duplicates-still-agree : S.lookup "Boundary#Pack"
  (S.constructorTable (E.family ∷ second ∷ []))
  ≡ findCtor "Boundary#Pack" (E.family ∷ second ∷ [])
duplicates-still-agree = S.constructor-lookup-agrees "Boundary#Pack" (E.family ∷ second ∷ [])

duplicate-keys-rejected : ∀ {A : Set} name (first second : A) rest
  → S.Unique ((name , first) ∷ (name , second) ∷ rest) → ⊥
duplicate-keys-rejected name first second rest
  (S.unique∷ (S.fresh∷ different fresh) unique) = different refl

duplicate-constructors-rejected :
  S.Unique (S.constructorTable (E.family ∷ second ∷ [])) → ⊥
duplicate-constructors-rejected =
  duplicate-keys-rejected "Boundary#Pack" (E.family , E.ctor) (second , E.ctor) []
duplicate-families-rejected :
  S.Unique (S.familyTable (E.family ∷ E.family ∷ [])) → ⊥
duplicate-families-rejected =
  duplicate-keys-rejected "Boundary#Packed" E.family E.family []
duplicate-globals-rejected :
  S.Unique (("answer" , E.answer) ∷ ("answer" , E.answer) ∷ []) → ⊥
duplicate-globals-rejected = duplicate-keys-rejected "answer" E.answer E.answer []

global-member-found : S.lookup "Boundary#answer" (S.Snapshot.globals E.snapshot)
  ≡ just E.answer
global-member-found = S.member-lookup (S.Snapshot.global-keys E.snapshot) (here refl)
family-missing : S.lookup "Other#Packed" (S.familyTable (E.family ∷ [])) ≡ nothing
family-missing = refl
ctor-missing : S.lookup "Other#Pack" (S.constructorTable (E.family ∷ [])) ≡ nothing
ctor-missing = refl

opaque-entry : S.Global
opaque-entry = S.global tm-atom_type nothing
opaque-type-present :
  Signature.type-of (S.signature (("opaque" , opaque-entry) ∷ [])) "opaque" ≡ just tm-atom_type
opaque-type-present = S.global-type-found
  {globals = ("opaque" , opaque-entry) ∷ []} {key = "opaque"} {entry = opaque-entry} refl
opaque-body-absent :
  Signature.body (S.signature (("opaque" , opaque-entry) ∷ [])) "opaque" ≡ nothing
opaque-body-absent = refl
-- Snapshot replacement cannot mutate an already constructed signature.
old-body-visible : Signature.body (S.Snapshot.sig E.snapshot) "Boundary#answer"
  ≡ just (tm-atom_lit "answer")
old-body-visible = E.global-found
new-body-hidden :
  Signature.body (S.signature (("Boundary#answer" , opaque-entry) ∷ [])) "Boundary#answer" ≡ nothing
new-body-hidden = refl
