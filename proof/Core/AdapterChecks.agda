------------------------------------------------------------------------
-- M2c: the four remaining adapter obligations, as CHECKED preconditions
-- rather than unproved trust.
--
-- `Core.AdapterConstruction` (M2b) discharged obligations (3), (4), (6)
-- and (8) by DEFINING the extraction. Four remained: (1) name encoding,
-- (2) table extraction, (5) certification flags, (7) hidden bodies.
--
-- Reading the actual producer changes the picture. `Cure.Core.ProofSnapshot`
-- ALREADY rejects payloads that violate (5) and (7), and already refuses
-- names that violate (1)'s encoding discipline:
--
--   proof_snapshot.ex:94   ensure!(subset?(set, keys(defs)), :unknown_certified_global)
--   proof_snapshot.ex:97   ensure!(subset?(certified, totality_certified),
--                                 :inconsistent_certification)
--   proof_snapshot.ex:282  ensure!(text != "" and all printable ASCII,
--                                 :unsupported_name_encoding)
--
-- So these are not silent assumptions: they are FAIL-CLOSED CHECKS the
-- producer performs. The formal gap is that the Agda development did not
-- MODEL those checks, so a consumer had to take them on trust.
--
-- This module closes that gap for (5) and (7) exactly, and states (1) and
-- (2) precisely enough to say what remains.
--
-- (5) and (7) are PROVED here. Both are subset relations between host
-- lists, and a `Checked` payload only exists when the producer's checks
-- passed, so the relations hold BY CONSTRUCTION.
--
-- (1) is PARTIAL, and the reason is a recorded finding rather than a
-- gap. `Name` is `String`, and the standard library offers only
-- `primStringToList` injectivity -- the round-trip needed for a
-- character-faithful encoding exists solely as a postulate in
-- `Data.String.Unsafe`, which this development refuses to use. The wire
-- layer already handles this by INTERNING names as table indices
-- (`Core.Wire`), and `name-encoding-interned` below does the same: the
-- encoding is partial and its injectivity is proved for the names a
-- table actually contains. The full `String -> Name` injectivity that
-- `RepresentationBoundary.name-encoding-injective` asks for is NOT
-- claimed.
--
-- (2) is NOT proved and is not provable from the payload alone: it says
-- the host payload IS the registry, which is a fact about Elixir state
-- that no Agda type can witness. It stays explicit trust, and
-- `remaining` records it.
--
-- This module introduces no postulate, no hole and no checking
-- override.
------------------------------------------------------------------------
module Core.AdapterChecks where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Core.Signature using (nothing≠just; just-inj)
open import Core.Syntax using (Name)
open import Core.HostTable using (HostTable; Unique)
import Core.HostTable as HT
open import Core.AdapterConstruction using (Payload; extract-names)

------------------------------------------------------------------------
-- The producer's checks, as a type.
--
-- `Cure.Core.ProofSnapshot.capture/1` rejects a payload unless
--   * every certified name is a registered global, and
--   * every certified name is also totality-certified.
-- A `Validated` payload is one that passed BOTH. There is no way to
-- build one otherwise, which is what makes the obligations below
-- theorems rather than assumptions.
------------------------------------------------------------------------

record Validated : Set where
  constructor validated
  field
    payload : Payload
    -- (5) certified ⊆ totality-certified. This is
    -- `proof_snapshot.ex:97`'s `ensure!`.
    certified-subset-totality :
      ∀ name → name ∈ Payload.certified payload → name ∈ Payload.totality payload
    -- (7) certified ⊆ global-names. This is `proof_snapshot.ex:94`'s
    -- `ensure!` restricted to the certified set.
    certified-subset-globals :
      ∀ name → name ∈ Payload.certified payload → name ∈ Payload.global-names payload
open Validated public

------------------------------------------------------------------------
-- (5) CERTIFICATION FLAGS, proved.
--
-- The obligation says: a name the host calls certified is also one it
-- calls totality-certified. That is exactly the field, so the theorem is
-- a projection -- and the POINT is that the projection is the only way
-- to obtain it. A consumer cannot get `flags-uninterpreted` for a
-- payload that failed the producer's check, because no `Validated`
-- value exists for such a payload.
------------------------------------------------------------------------

flags-uninterpreted : ∀ (v : Validated) name
  → name ∈ Payload.certified (payload v)
  → name ∈ Payload.totality (payload v)
flags-uninterpreted v = certified-subset-totality v

------------------------------------------------------------------------
-- (7) HIDDEN BODIES, proved.
--
-- Same shape: "no certified global is dropped" is the producer's own
-- check, so it holds by projection.
------------------------------------------------------------------------

hidden-bodies-captured : ∀ (v : Validated) name
  → name ∈ Payload.certified (payload v)
  → name ∈ Payload.global-names (payload v)
hidden-bodies-captured v = certified-subset-globals v

------------------------------------------------------------------------
-- The checks are NOT vacuous: a payload that violates either one has no
-- `Validated` value. Both refutations are constructive.
------------------------------------------------------------------------

-- A payload whose certified set is nonempty but whose globals are empty
-- fails (7).
globals-dropped : Payload
globals-dropped = record
  { family-names = []
  ; global-names = []
  ; alias-pairs  = []
  ; certified    = "Boundary#id" ∷ []
  ; totality     = "Boundary#id" ∷ []
  }

globals-dropped-refused : ¬ (∀ name → name ∈ Payload.certified globals-dropped
  → name ∈ Payload.global-names globals-dropped)
globals-dropped-refused h with h "Boundary#id" (here refl)
... | ()

-- A payload whose certified set is nonempty but whose totality set is
-- empty fails (5).
totality-dropped : Payload
totality-dropped = record
  { family-names = []
  ; global-names = "Boundary#id" ∷ []
  ; alias-pairs  = []
  ; certified    = "Boundary#id" ∷ []
  ; totality     = []
  }

totality-dropped-refused : ¬ (∀ name → name ∈ Payload.certified totality-dropped
  → name ∈ Payload.totality totality-dropped)
totality-dropped-refused h with h "Boundary#id" (here refl)
... | ()

------------------------------------------------------------------------
-- (1) NAME ENCODING, in the INTERNED form.
--
-- A character-faithful `String -> Name` encoding with a proved inverse
-- is not available here: the stdlib gives only `primStringToList`
-- injectivity, and the round-trip lives as a postulate in
-- `Data.String.Unsafe`, which this development does not use. `Core.Wire`
-- resolves this by INTERNING names as table indices; the same discipline
-- applies to the adapter.
--
-- The honest statement is therefore PARTIAL: encoding is defined only
-- for names a table contains, and it is injective THERE. That is enough
-- for every consumer, because the adapter only ever encodes names it
-- captured.
------------------------------------------------------------------------

index-of : (name : Name) (table : List Name) → Maybe ℕ
index-of name [] = nothing
index-of name (x ∷ table) with name ≟ x
... | yes same = just zero
... | no different with index-of name table
...   | nothing = nothing
...   | just i = just (suc i)

-- `index-of` skips the head when it does not match and recurses on the
-- TAIL, so the index it returns is relative to the table it was given
-- at that point. `lookup-at` mirrors that exactly: it walks the same
-- way, so the two compose.
lookup-at : ℕ → List Name → Maybe Name
lookup-at zero [] = nothing
lookup-at zero (x ∷ table) = just x
lookup-at (suc i) [] = nothing
lookup-at (suc i) (x ∷ table) = lookup-at i table

-- An index produced by `index-of` really points at that name.
index-of-sound : ∀ name table i
  → index-of name table ≡ just i → lookup-at i table ≡ just name
index-of-sound name [] i ()
index-of-sound name (x ∷ table) i found with name ≟ x
... | yes same = subst (λ index → lookup-at index (x ∷ table) ≡ just name)
                       (just-inj found) (cong just (sym same))
... | no different with index-of name table in nested
...   | nothing = ⊥-elim (nothing≠just found)
...   | just j = subst (λ index → lookup-at index (x ∷ table) ≡ just name)
                       (just-inj found) (index-of-sound name table j nested)

-- THEOREM (obligation 1, interned form). Encoding a name that IS in the
-- table, then decoding the index, returns that name. This is the
-- round-trip the adapter needs, proved without a string axiom.
name-encoding-interned : ∀ (name : Name) (table : List Name)
  → name ∈ table
  → ∀ i → index-of name table ≡ just i → lookup-at i table ≡ just name
name-encoding-interned name table member i found = index-of-sound name table i found

-- A successful lookup means the name IS in the table.
lookup-at-member : ∀ (i : ℕ) (table : List Name) name
  → lookup-at i table ≡ just name → name ∈ table
lookup-at-member zero [] name ()
lookup-at-member zero (x ∷ table) name found with just-inj found
... | refl = here refl
lookup-at-member (suc i) [] name ()
lookup-at-member (suc i) (x ∷ table) name found =
  there (lookup-at-member i table name found)

-- The encoding is PARTIAL, and honestly so: a name absent from the table
-- has no index at all. This is the contrapositive of `index-of-sound`,
-- which is why it needs no separate induction.
absent-name : ∀ (name : Name) (table : List Name)
  → ¬ (name ∈ table)
  → index-of name table ≡ nothing
absent-name name table absent with index-of name table in found
... | nothing = refl
... | just i = ⊥-elim (absent (lookup-at-member i table name
                                  (index-of-sound name table i found)))

------------------------------------------------------------------------
-- (2) TABLE EXTRACTION is NOT discharged, and cannot be.
--
-- The obligation says the host payload IS the registry, i.e. that
-- `Cure.Core.ProofSnapshot.capture/1` faithfully flattened Elixir state
-- into `HostPayload`. No Agda value can witness a fact about Elixir
-- state; a field claiming it would be exactly the kind of unproved
-- assumption this milestone exists to remove. It stays explicit trust.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The M2c ledger.
------------------------------------------------------------------------

record Ledger : Set where
  constructor ledger
  field
    discharged : List String
    remaining  : List String
open Ledger public

m2c-ledger : Ledger
m2c-ledger = ledger
  ( "(5) flags-uninterpreted: the producer rejects a payload violating it (flags-uninterpreted)"
  ∷ "(7) hidden-bodies-captured: the producer rejects a payload violating it (hidden-bodies-captured)"
  ∷ "(1) name-encoding: proved in INTERNED form, with a partial encoding (name-encoding-interned)"
  ∷ [] )
  ( "(2) extracted: that the host payload IS the registry is a fact about Elixir state,"
  ∷ "    which no Agda type can witness; it stays explicit trust (extracted)"
  ∷ [] )

discharged-nonempty : ¬ (discharged m2c-ledger ≡ [])
discharged-nonempty ()

remaining-nonempty : ¬ (remaining m2c-ledger ≡ [])
remaining-nonempty ()
