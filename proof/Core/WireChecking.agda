{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Tag 20 checking requests: actual inference and kind guards precede
-- bounded model comparison. Rejection/unknown diagnostics are preserved.
------------------------------------------------------------------------
module Core.WireChecking where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax using (Name)
open import Core.Signature using (nothing≠just; just-inj)
import Core.CheckedAdmission as Source
import Core.NormalizingAdmission as Admission
import Core.Wire as W
import Core.WireSnapshot as S
import Core.WireCaller as Caller
import Core.WireConversion as C
open import Core.WireCertificate using (Codec)
open import Core.WireCombinators using (both; tagged; iso; bind)
open Codec
open Admission using (Request; request)

checking : List Name → Codec Request
checking table = tagged 20 (iso
  (both (S.term table) (both (Caller.recipe table) (both (Caller.recipe table)
    (both (S.term table) (Caller.recipe table)))))
  (λ { (subject , recipe , kind , goal , goal-kind) → request subject recipe kind goal goal-kind })
  (λ q → Request.subject q , Request.subject-recipe q , Request.inferred-kind-recipe q ,
    Request.goal q , Request.goal-kind-recipe q) (λ q → refl))
to-node : List Name → Request → Maybe W.Node
to-node table = write (checking table)
from-node : List Name → W.Node → Maybe Request
from-node table = read (checking table)
fidelity : ∀ table query node → to-node table query ≡ just node → from-node table node ≡ just query
fidelity table = faithful (checking table)
encode : List Name → Request → Maybe (List Char)
encode table query = C.map W.encode (to-node table query)
decode : List Name → List Char → Maybe Request
decode table characters = bind (W.decode characters) (from-node table)
character-fidelity : ∀ table query node → to-node table query ≡ just node
  → decode table (W.encode node) ≡ just query
character-fidelity table query node written rewrite W.decode-encode node = fidelity table query node written
roundtrip : ∀ table query characters → encode table query ≡ just characters → decode table characters ≡ just query
roundtrip table query characters found with to-node table query in written
... | nothing = ⊥-elim (nothing≠just found)
... | just node with just-inj found
... | refl = character-fidelity table query node written

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
