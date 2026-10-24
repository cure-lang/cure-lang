{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Opt-in residual replay of the EXISTING tag-20 checking codec. Decoding
-- and exact request pinning remain separate from checked native admission.
------------------------------------------------------------------------
module Core.WireResidualChecking where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Signature using (just-inj)
import Core.CheckedAdmission as Source
import Core.ResidualAdmission as Admission
open Admission using (Request)
open import Core.WireChecking public using
  (checking; to-node; from-node; fidelity; encode; decode; character-fidelity; roundtrip)

module Replay {source table certificate-chars} (source-checked : Source.Checked source table certificate-chars) where
  DataChecked : Request → Set
  DataChecked = Admission.Replay.Checked source-checked
  verify-data : ℕ → (query : Request) → Admission.Result (DataChecked query)
  verify-data = Admission.Replay.verify source-checked
  record Checked (fuel : ℕ) (characters : List Char) : Set where
    field
      query : Request
      decoded : decode table characters ≡ just query
      admission : DataChecked query
      verified : verify-data fuel query ≡ Admission.accepted admission
  package : ∀ fuel characters query → decode table characters ≡ just query
    → (result : Admission.Result (DataChecked query)) → verify-data fuel query ≡ result
    → Admission.Result (Checked fuel characters)
  package fuel characters query decoded (Admission.rejected reason) verified = Admission.rejected reason
  package fuel characters query decoded (Admission.accepted admission) verified = Admission.accepted record
    { query = query ; decoded = decoded ; admission = admission ; verified = verified }
  finish : ∀ fuel characters query → decode table characters ≡ just query → Admission.Result (Checked fuel characters)
  finish fuel characters query decoded = package fuel characters query decoded (verify-data fuel query) refl
  package-status : ∀ fuel characters query decoded result verified
    → Admission.present (package fuel characters query decoded result verified) ≡ Admission.present result
  package-status fuel characters query decoded (Admission.rejected reason) verified = refl
  package-status fuel characters query decoded (Admission.accepted admission) verified = refl
  finish-status : ∀ fuel characters query decoded
    → Admission.present (finish fuel characters query decoded) ≡ Admission.present (verify-data fuel query)
  finish-status fuel characters query decoded = package-status fuel characters query decoded (verify-data fuel query) refl
  dispatch : ∀ fuel characters (result : Maybe Request) → decode table characters ≡ result
    → Admission.Result (Checked fuel characters)
  dispatch fuel characters nothing decoded = Admission.rejected Admission.malformed-wire
  dispatch fuel characters (just query) decoded = finish fuel characters query decoded
  verify : (fuel : ℕ) (characters : List Char) → Admission.Result (Checked fuel characters)
  verify fuel characters = dispatch fuel characters (decode table characters) refl
  dispatch-status : ∀ fuel characters result decoded query → result ≡ just query
    → Admission.present (dispatch fuel characters result decoded) ≡ Admission.present (verify-data fuel query)
  dispatch-status fuel characters nothing decoded query ()
  dispatch-status fuel characters (just query) decoded .query refl = finish-status fuel characters query decoded
  verify-decoded : ∀ fuel characters query → decode table characters ≡ just query
    → Admission.present (verify fuel characters) ≡ Admission.present (verify-data fuel query)
  verify-decoded fuel characters query decoded =
    dispatch-status fuel characters (decode table characters) refl query decoded
  pin : ∀ {fuel characters} → (checked : Checked fuel characters) → (query : Request)
    → decode table characters ≡ just query → DataChecked query
  pin checked query decoded = subst DataChecked
    (just-inj (trans (sym (Checked.decoded checked)) decoded)) (Checked.admission checked)
