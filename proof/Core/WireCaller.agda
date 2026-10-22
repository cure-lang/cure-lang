{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Tag 19 contains a right-nested product of eight caller request fields.
-- Character parsing is data-only; semantic replay checks the full frame.
------------------------------------------------------------------------
module Core.WireCaller where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax using (Name)
open import Core.Signature using (nothing≠just; just-inj)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as P
import Core.CallerAdmission as Caller
import Core.Wire as W
import Core.WireSnapshot as S
import Core.WireRecipe as RecipeWire
import Core.WireConversion as C
open import Core.WireCombinators using (both; many; tagged; iso; bind)
open import Core.WireCertificate using (Codec)
open Codec
open Caller using (Request; request)

recipe : List Name → Codec Recipe
recipe table = record
  { write = RecipeWire.to-node table ; read = RecipeWire.from-node table ; faithful = RecipeWire.fidelity table }
caller : List Name → Codec Request
caller table = tagged 19 (iso
  (both (S.telescope table) (both (many (recipe table)) (both (many (S.term table))
    (both (many (recipe table)) (both (S.term table) (both (S.term table)
      (both (recipe table) (recipe table))))))))
  (λ { (tele , kinds , args , arg-recipes , t , ty , body , kind) →
    request tele kinds args arg-recipes t ty body kind })
  (λ q → Request.bindings q , Request.kind-recipes q , Request.arguments q , Request.argument-recipes q ,
    Request.subject q , Request.goal q , Request.subject-recipe q , Request.goal-recipe q)
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

module Replay {source table certificate-chars} (source-checked : P.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  record Checked (characters : List Char) : Set where
    field
      query : Request
      decoded : decode table characters ≡ just query
      admission : R.Checked query
      verified : R.verify query ≡ just admission
  package : ∀ characters query → decode table characters ≡ just query
    → (result : Maybe (R.Checked query)) → R.verify query ≡ result → Maybe (Checked characters)
  package characters query decoded nothing verified = nothing
  package characters query decoded (just admission) verified = just record
    { query = query ; decoded = decoded ; admission = admission ; verified = verified }
  finish : ∀ characters query → decode table characters ≡ just query → Maybe (Checked characters)
  finish characters query decoded = package characters query decoded (R.verify query) refl
  package-status : ∀ characters query decoded result verified
    → P.present (package characters query decoded result verified) ≡ P.present result
  package-status characters query decoded nothing verified = refl
  package-status characters query decoded (just admission) verified = refl
  finish-status : ∀ characters query decoded
    → P.present (finish characters query decoded) ≡ P.present (R.verify query)
  finish-status characters query decoded = package-status characters query decoded (R.verify query) refl
  dispatch : ∀ characters (result : Maybe Request) → decode table characters ≡ result → Maybe (Checked characters)
  dispatch characters nothing decoded = nothing
  dispatch characters (just query) decoded = finish characters query decoded
  verify : (characters : List Char) → Maybe (Checked characters)
  verify characters = dispatch characters (decode table characters) refl
  dispatch-status : ∀ characters result decoded query → result ≡ just query
    → P.present (dispatch characters result decoded) ≡ P.present (R.verify query)
  dispatch-status characters nothing decoded query ()
  dispatch-status characters (just query) decoded .query refl = finish-status characters query decoded
  verify-decoded : ∀ characters query → decode table characters ≡ just query
    → P.present (verify characters) ≡ P.present (R.verify query)
  verify-decoded characters query decoded =
    dispatch-status characters (decode table characters) refl query decoded
  pin : ∀ {characters} → (checked : Checked characters) → (query : Request)
    → decode table characters ≡ just query → R.Checked query
  pin checked query decoded = subst R.Checked
    (just-inj (trans (sym (Checked.decoded checked)) decoded)) (Checked.admission checked)
