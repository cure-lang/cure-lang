{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Tag 21 is a separate opt-in packet. Its body carries the unchanged
-- tag-19 caller, the open inferred-kind recipe, and argument kind recipes.
-- Fuel and residual policy are verifier configuration, not packet claims.
------------------------------------------------------------------------
module Core.WireArgumentCaller where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax using (Name)
open import Core.Signature using (nothing≠just; just-inj)
import Core.CheckedAdmission as P
import Core.ArgumentAdmission as Argument
import Core.ArgumentCallerAdmission as Caller
import Core.ResidualCallerAdmission as Residual
import Core.WireCaller as Existing
import Core.Wire as W
import Core.WireConversion as C
open import Core.WireCombinators using (both; many; tagged; iso; bind)
open import Core.WireCertificate using (Codec)
open Codec
open Caller using (Request; request)

caller : List Name → Codec Request
caller table = tagged 21 (iso
  (both (Existing.caller table) (both (Existing.recipe table) (many (Existing.recipe table))))
  (λ { (call , kind , kinds) → request (Residual.request call kind) kinds })
  (λ q → Residual.Request.caller (Request.caller q) ,
    Residual.Request.inferred-kind-recipe (Request.caller q) , Request.argument-kind-recipes q)
  (λ q → refl))
to-node : List Name → Request → Maybe W.Node
to-node table = write (caller table)
from-node : List Name → W.Node → Maybe Request
from-node table = read (caller table)
fidelity : ∀ table query node → to-node table query ≡ just node → from-node table node ≡ just query
fidelity table = faithful (caller table)
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

module Replay {source table certificate-chars} (source-checked : P.Checked source table certificate-chars)
  (fuel : ℕ) (opts : Argument.Options) where
  module R = Caller.Replay source-checked
  verify-data : (query : Request) → Maybe (R.Checked query)
  verify-data = R.verify fuel opts
  record Checked (characters : List Char) : Set where
    field
      query : Request
      decoded : decode table characters ≡ just query
      admission : R.Checked query
      verified : verify-data query ≡ just admission
  package : ∀ characters query → decode table characters ≡ just query
    → (result : Maybe (R.Checked query)) → verify-data query ≡ result → Maybe (Checked characters)
  package characters query decoded nothing verified = nothing
  package characters query decoded (just admission) verified = just record
    { query = query ; decoded = decoded ; admission = admission ; verified = verified }
  finish : ∀ characters query → decode table characters ≡ just query → Maybe (Checked characters)
  finish characters query decoded = package characters query decoded (verify-data query) refl
  package-status : ∀ characters query decoded result verified
    → P.present (package characters query decoded result verified) ≡ P.present result
  package-status characters query decoded nothing verified = refl
  package-status characters query decoded (just admission) verified = refl
  finish-status : ∀ characters query decoded
    → P.present (finish characters query decoded) ≡ P.present (verify-data query)
  finish-status characters query decoded = package-status characters query decoded (verify-data query) refl
  dispatch : ∀ characters (result : Maybe Request) → decode table characters ≡ result → Maybe (Checked characters)
  dispatch characters nothing decoded = nothing
  dispatch characters (just query) decoded = finish characters query decoded
  verify : (characters : List Char) → Maybe (Checked characters)
  verify characters = dispatch characters (decode table characters) refl
  dispatch-status : ∀ characters result decoded query → result ≡ just query
    → P.present (dispatch characters result decoded) ≡ P.present (verify-data query)
  dispatch-status characters nothing decoded query ()
  dispatch-status characters (just query) decoded .query refl = finish-status characters query decoded
  verify-decoded : ∀ characters query → decode table characters ≡ just query
    → P.present (verify characters) ≡ P.present (verify-data query)
  verify-decoded characters query decoded =
    dispatch-status characters (decode table characters) refl query decoded
  pin : ∀ {characters} → (checked : Checked characters) → (query : Request)
    → decode table characters ≡ just query → R.Checked query
  pin checked query decoded = subst R.Checked
    (just-inj (trans (sym (Checked.decoded checked)) decoded)) (Checked.admission checked)
