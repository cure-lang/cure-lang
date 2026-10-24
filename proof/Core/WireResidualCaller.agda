{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- TWO existing EOF-checked packets: caller data and inferred-kind recipe.
-- Neither packet supplies a context proof or a normalized-equality flag.
------------------------------------------------------------------------
module Core.WireResidualCaller where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax using (Name)
open import Core.Signature using (nothing≠just; just-inj)
import Core.CheckedAdmission as P
import Core.ResidualCallerAdmission as Caller
import Core.WireCaller as Existing
import Core.WireRecipe as Recipe
import Core.WireConversion as C
open Caller using (Request; request)

encode : List Name → Request → Maybe (List Char × List Char)
encode table query = C.pair _,_ (Existing.encode table (Caller.Request.caller query))
  (Recipe.encode table (Caller.Request.inferred-kind-recipe query))
decode : List Name → List Char → List Char → Maybe Request
decode table caller-chars kind-chars = C.pair request (Existing.decode table caller-chars) (Recipe.decode table kind-chars)
roundtrip : ∀ table query caller-chars kind-chars → encode table query ≡ just (caller-chars , kind-chars)
  → decode table caller-chars kind-chars ≡ just query
roundtrip table query caller-chars kind-chars encoded
  with Existing.encode table (Caller.Request.caller query) in caller-encoded
... | nothing = ⊥-elim (nothing≠just encoded)
... | just cs with Recipe.encode table (Caller.Request.inferred-kind-recipe query) in kind-encoded
... | nothing = ⊥-elim (nothing≠just encoded)
... | just ks with just-inj encoded
... | refl rewrite Existing.roundtrip table (Caller.Request.caller query) cs caller-encoded
  | Recipe.roundtrip table (Caller.Request.inferred-kind-recipe query) ks kind-encoded = refl

module Replay {source table certificate-chars} (source-checked : P.Checked source table certificate-chars) (fuel : ℕ) where
  module R = Caller.Replay source-checked
  verify-data : (query : Request) → Maybe (R.Checked query)
  verify-data = R.verify fuel
  record Checked (caller-chars kind-chars : List Char) : Set where
    field
      query : Request
      decoded : decode table caller-chars kind-chars ≡ just query
      admission : R.Checked query
      verified : verify-data query ≡ just admission
  package : ∀ caller-chars kind-chars query → decode table caller-chars kind-chars ≡ just query
    → (result : Maybe (R.Checked query)) → verify-data query ≡ result → Maybe (Checked caller-chars kind-chars)
  package caller-chars kind-chars query decoded nothing verified = nothing
  package caller-chars kind-chars query decoded (just admission) verified = just record
    { query = query ; decoded = decoded ; admission = admission ; verified = verified }
  finish : ∀ caller-chars kind-chars query → decode table caller-chars kind-chars ≡ just query → Maybe (Checked caller-chars kind-chars)
  finish caller-chars kind-chars query decoded = package caller-chars kind-chars query decoded (verify-data query) refl
  package-status : ∀ caller-chars kind-chars query decoded result verified
    → P.present (package caller-chars kind-chars query decoded result verified) ≡ P.present result
  package-status caller-chars kind-chars query decoded nothing verified = refl
  package-status caller-chars kind-chars query decoded (just admission) verified = refl
  finish-status : ∀ caller-chars kind-chars query decoded
    → P.present (finish caller-chars kind-chars query decoded) ≡ P.present (verify-data query)
  finish-status caller-chars kind-chars query decoded = package-status caller-chars kind-chars query decoded (verify-data query) refl
  dispatch : ∀ caller-chars kind-chars (result : Maybe Request) → decode table caller-chars kind-chars ≡ result → Maybe (Checked caller-chars kind-chars)
  dispatch caller-chars kind-chars nothing decoded = nothing
  dispatch caller-chars kind-chars (just query) decoded = finish caller-chars kind-chars query decoded
  verify : (caller-chars kind-chars : List Char) → Maybe (Checked caller-chars kind-chars)
  verify caller-chars kind-chars = dispatch caller-chars kind-chars (decode table caller-chars kind-chars) refl
  dispatch-status : ∀ caller-chars kind-chars result decoded query → result ≡ just query
    → P.present (dispatch caller-chars kind-chars result decoded) ≡ P.present (verify-data query)
  dispatch-status caller-chars kind-chars nothing decoded query ()
  dispatch-status caller-chars kind-chars (just query) decoded .query refl = finish-status caller-chars kind-chars query decoded
  verify-decoded : ∀ caller-chars kind-chars query → decode table caller-chars kind-chars ≡ just query
    → P.present (verify caller-chars kind-chars) ≡ P.present (verify-data query)
  verify-decoded caller-chars kind-chars query decoded =
    dispatch-status caller-chars kind-chars (decode table caller-chars kind-chars) refl query decoded
  pin : ∀ {caller-chars kind-chars} → (checked : Checked caller-chars kind-chars) → (query : Request)
    → decode table caller-chars kind-chars ≡ just query → R.Checked query
  pin checked query decoded = subst R.Checked
    (just-inj (trans (sym (Checked.decoded checked)) decoded)) (Checked.admission checked)
