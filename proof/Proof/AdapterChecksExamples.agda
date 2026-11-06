------------------------------------------------------------------------
-- M2c examples: the checked-payload construction, inhabited, with the
-- controls that keep each discharge from being vacuous.
--
-- `Core.AdapterChecks` proves obligations (5) and (7) from the producer's
-- own fail-closed checks, and obligation (1) in the interned form the
-- wire layer already uses. A theorem about a checked payload is only
-- useful if such a payload EXISTS and if the checks can actually FAIL,
-- so this module supplies both.
------------------------------------------------------------------------
module Proof.AdapterChecksExamples where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_; length)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Core.Syntax using (Name)
open import Core.AdapterConstruction using (Payload)
open import Core.AdapterChecks

------------------------------------------------------------------------
-- A payload that PASSES both producer checks: one global, certified and
-- totality-certified.
------------------------------------------------------------------------

good : Payload
good = record
  { family-names = "Boundary#Packed" ∷ []
  ; global-names = "Boundary#id" ∷ []
  ; alias-pairs  = []
  ; certified    = "Boundary#id" ∷ []
  ; totality     = "Boundary#id" ∷ []
  }

good-validated : Validated
good-validated = validated good
  (λ { name (here refl) → here refl })
  (λ { name (here refl) → here refl })

------------------------------------------------------------------------
-- (5) CERTIFICATION FLAGS, exercised at a concrete name.
------------------------------------------------------------------------

good-flags : ∀ name → name ∈ Payload.certified good → name ∈ Payload.totality good
good-flags = flags-uninterpreted good-validated

good-flags-id : "Boundary#id" ∈ Payload.totality good
good-flags-id = flags-uninterpreted good-validated "Boundary#id" (here refl)

------------------------------------------------------------------------
-- (7) HIDDEN BODIES, exercised at a concrete name.
------------------------------------------------------------------------

good-bodies : ∀ name → name ∈ Payload.certified good → name ∈ Payload.global-names good
good-bodies = hidden-bodies-captured good-validated

good-bodies-id : "Boundary#id" ∈ Payload.global-names good
good-bodies-id = hidden-bodies-captured good-validated "Boundary#id" (here refl)

------------------------------------------------------------------------
-- NEGATIVE CONTROLS for (5) and (7).
--
-- Each exhibits a payload that violates the corresponding producer
-- check. No `Validated` value exists for either, which is exactly what
-- makes the theorems non-vacuous: they cannot be obtained for a payload
-- the producer would have rejected.
------------------------------------------------------------------------

-- (5) fails: certified but not totality-certified.
bad-totality : Payload
bad-totality = record
  { family-names = []
  ; global-names = "Boundary#id" ∷ []
  ; alias-pairs  = []
  ; certified    = "Boundary#id" ∷ []
  ; totality     = []
  }

bad-totality-refused : ¬ (∀ name → name ∈ Payload.certified bad-totality
  → name ∈ Payload.totality bad-totality)
bad-totality-refused h with h "Boundary#id" (here refl)
... | ()

-- (7) fails: certified but the global was dropped.
bad-globals : Payload
bad-globals = record
  { family-names = []
  ; global-names = []
  ; alias-pairs  = []
  ; certified    = "Boundary#id" ∷ []
  ; totality     = "Boundary#id" ∷ []
  }

bad-globals-refused : ¬ (∀ name → name ∈ Payload.certified bad-globals
  → name ∈ Payload.global-names bad-globals)
bad-globals-refused h with h "Boundary#id" (here refl)
... | ()

------------------------------------------------------------------------
-- (1) NAME ENCODING, in the interned form.
--
-- A name that IS in the table encodes to an index that decodes back to
-- it. The table is the one the adapter captured, so every name it needs
-- to encode is present by construction.
------------------------------------------------------------------------

table : List Name
table = "Boundary#Packed" ∷ "Boundary#Box" ∷ "Boundary#id" ∷ []

-- The first name encodes to index 0 and decodes back.
packed-index : index-of "Boundary#Packed" table ≡ just zero
packed-index = refl

packed-roundtrip : lookup-at zero table ≡ just "Boundary#Packed"
packed-roundtrip = index-of-sound "Boundary#Packed" table zero refl

-- The third name encodes to index 2 and decodes back.
id-index : index-of "Boundary#id" table ≡ just (suc (suc zero))
id-index = refl

id-roundtrip : lookup-at (suc (suc zero)) table ≡ just "Boundary#id"
id-roundtrip = index-of-sound "Boundary#id" table (suc (suc zero)) refl

-- The general theorem, instantiated: any name in the table round-trips.
packed-general : ∀ i → index-of "Boundary#Packed" table ≡ just i
  → lookup-at i table ≡ just "Boundary#Packed"
packed-general = name-encoding-interned "Boundary#Packed" table (here refl)

------------------------------------------------------------------------
-- (1) is PARTIAL, and the negative control shows why that is honest
-- rather than a limitation to paper over: a name absent from the table
-- has NO index. The adapter only ever encodes names it captured, so the
-- partiality never bites in practice -- but it is real.
------------------------------------------------------------------------

-- `"Boundary#Missing"` differs from each of the three table entries, so
-- it is in none of them. One lemma per spelling; each is refuted by the
-- mismatched character lists.
missing≠packed : toList "Boundary#Missing" ≡ toList "Boundary#Packed" → ⊥
missing≠packed ()

missing≠box : toList "Boundary#Missing" ≡ toList "Boundary#Box" → ⊥
missing≠box ()

missing≠id : toList "Boundary#Missing" ≡ toList "Boundary#id" → ⊥
missing≠id ()

absent-has-no-index : index-of "Boundary#Missing" table ≡ nothing
absent-has-no-index = absent-name "Boundary#Missing" table absent
  where
    absent : ¬ ("Boundary#Missing" ∈ table)
    absent (here same) = missing≠packed (cong toList same)
    absent (there (here same)) = missing≠box (cong toList same)
    absent (there (there (here same))) = missing≠id (cong toList same)
    absent (there (there (there ())))

------------------------------------------------------------------------
-- The ledger, instantiated: three discharged, one remaining.
------------------------------------------------------------------------

m2c-split : length (discharged m2c-ledger) ≡ 3 × length (remaining m2c-ledger) ≡ 2
m2c-split = refl , refl
