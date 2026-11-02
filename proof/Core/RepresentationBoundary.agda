------------------------------------------------------------------------
-- The representation boundary, stated as data rather than prose.
--
-- `PLAN.md` §7 requires that, if a deliverable keeps an adapter in the
-- trusted computing base, its exact obligations are stated in the
-- claim. This module makes that statement MECHANICAL: the boundary is
-- a record whose fields are the specific facts an adapter must
-- establish, and a `Boundary` value is the claim "these facts hold".
--
-- Nothing here proves those facts. That is the point. The record
-- exists so that
--
--   * a consumer of a representation claim must CONSUME a `Boundary`
--     value, making the adapter trust visible at every use site
--     instead of being buried in a comment;
--   * adding a new adapter obligation is a type error until the
--     record is extended, so the trust surface cannot grow silently;
--   * the obligations that ARE proved (`Core.HostTable`) are listed
--     separately from the ones that are NOT, so the split is auditable.
--
-- This module introduces no postulate, no hole and no checking
-- override. It is a specification of what remains to be proved.
------------------------------------------------------------------------
module Core.RepresentationBoundary where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax using (Name)
open import Core.HostTable using (HostTable; Unique)
import Core.HostTable as HT

------------------------------------------------------------------------
-- What the host actually hands us.
--
-- An adapter reads an Elixir `Env` and produces this. The fields are
-- deliberately HOST-SHAPED: strings as they appear, an
-- unordered-by-construction keyed collection flattened to a list, and
-- the raw certification flags as booleans. Turning this into the
-- formal `Core.ExecutableSnapshot.Input` is the adapter's job, and
-- every step of that job is an obligation below.
------------------------------------------------------------------------

record HostPayload : Set where
  constructor host-payload
  field
    -- The registry entries, flattened from the host's keyed maps.
    -- Order is whatever the adapter chose; duplicates are possible in
    -- principle and must be rejected, not silently collapsed.
    family-names : List String
    global-names : List String
    -- Alias spellings the host would resolve, kept separate from keys.
    aliases : List (String × String)
    -- Raw certification claims, exactly as the host stores them.
    certified : List String
    totality-certified : List String
open HostPayload public

-- First-match over a plain list of name spellings, as the host stores
-- declaration order. This is what "the adapter preserved order" is
-- stated against: the extracted table's first match for a name must be
-- the host's own first match.
host-first-match : String → List String → Maybe String
host-first-match key [] = nothing
host-first-match key (name ∷ rest) with key ≟ name
... | yes same = just name
... | no different = host-first-match key rest

------------------------------------------------------------------------
-- The obligations.
--
-- Each field names one thing an adapter must get right, and the
-- comment says which part is PROVED for the modelled slice
-- (`Core.HostTable`) and which is not.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    -- The host payload these obligations are about.
    payload : HostPayload

    -- (1) NAME IDENTITY. The host's string spellings correspond to
    -- formal `Name`s one-to-one on the captured set. NOT proved: this
    -- is the atom-interning and `Cure.Elab.Name.split/1` relationship,
    -- which lives in the Elixir implementation.
    name-encoding : String → Name

    name-encoding-injective : ∀ {a b} → name-encoding a ≡ name-encoding b → a ≡ b

    -- (2) TABLE EXTRACTION. The flattened table the adapter produces
    -- is a faithful presentation of the host's keyed collection.
    -- PROVED for the modelled part: given a duplicate-free
    -- presentation, `Core.HostTable.unique-lookup-stable` shows
    -- resolution is order-insensitive. NOT proved: that the adapter's
    -- flattening preserves the binding set.
    extracted : HostTable String

    -- (3) DUPLICATE REJECTION. The extracted table really is
    -- duplicate-free. PROVED as a DECISION PROCEDURE
    -- (`Core.HostTable.check-table`); that the adapter calls it, and
    -- that the host collection had no duplicates to begin with, are
    -- not proved. Stated as the property, not as a boolean, so a
    -- consumer gets the fact it actually needs.
    duplicates-rejected : Unique (HT.bindings extracted)

    -- (4) ALIAS SEPARATION. Alias spellings are kept out of the key
    -- table, so an alias cannot shadow a real key. PROVED as a law
    -- (`Core.HostTable.alias-cannot-shadow`) GIVEN that separation;
    -- the adapter's separation of the two tables is not proved.
    aliases-separate : ∀ key target → (key , target) ∈ HT.aliases extracted
      → ¬ ((key , target) ∈ HT.bindings extracted)

    -- (5) CERTIFICATION FLAGS. The booleans travel unchanged and are
    -- NOT interpreted as proofs. PROVED: the formal model records them
    -- as claims (`Core.ExecutableSnapshot`). NOT proved: that the
    -- host's flag means what the certificate verifier checks. Stated
    -- as the subset relation the executable actually maintains.
    flags-uninterpreted : ∀ name → name ∈ payload .certified → name ∈ payload .totality-certified

    -- (6) DECLARATION ORDER. Constructor order is preserved, because
    -- first-match lookup and coverage both depend on it. NOT proved:
    -- that the adapter reads the host's stored order rather than
    -- re-sorting. Stated as the ORDER-SENSITIVE lookup agreement the
    -- representation actually needs: the extracted table's first match
    -- for each name is the host's own first match.
    order-preserved : ∀ name → HT.host-key name (HT.bindings extracted)
                      ≡ host-first-match name (payload .family-names)

    -- (7) HIDDEN BODIES. Uncertified raw bodies are still captured, so
    -- replay can check them. NOT proved: that the adapter does not
    -- filter them. Stated as "no name is dropped": every certified
    -- global is also a captured global.
    hidden-bodies-captured : ∀ name → name ∈ payload .certified → name ∈ payload .global-names

    -- (8) SIGNATURE IMMUTABILITY. One signature is used for
    -- declaration replay, evaluation, readback and comparison. NOT
    -- proved: that the host does not mutate its registry mid-check.
    -- Stated as the property a mutation would violate: every stage
    -- observes the SAME extracted table, so a mid-check mutation
    -- would have to produce a different `Boundary`, not a different
    -- answer under this one.
    signature-immutable : ∀ (stage : ℕ) name
      → HT.host-key name (HT.bindings extracted)
      ≡ HT.host-key name (HT.bindings extracted)

------------------------------------------------------------------------
-- The proved/assumed split, as a value a reader can inspect.
--
-- `proved` lists the facts `Core.HostTable` establishes; `assumed`
-- lists the adapter obligations that remain. A consumer that needs the
-- full claim must take a `Boundary`; a consumer that only needs the
-- resolution laws can take `Core.HostTable` alone.
--
-- M2b UPDATE. `Core.AdapterConstruction` then asked which of the eight
-- fields FOLLOW FROM THE ADAPTER'S DEFINITION rather than from an
-- assumption, and proved four of them:
--
--   (6) order-preserved     -- `AdapterConstruction.order-preserved`
--   (3) duplicates-rejected -- `AdapterConstruction.duplicates-rejected`
--   (4) aliases-separate    -- `AdapterConstruction.aliases-separate`
--   (8) signature-immutable -- `AdapterConstruction.signature-immutable-real`
--
-- Obligation (8) deserves a warning: as stated HERE its two sides are
-- syntactically identical, so it is proved by `refl` for ANY function
-- and cannot be violated. `Core.AdapterConstruction` replaces it with a
-- version that quantifies over two DIFFERENT observations, which is
-- falsifiable and therefore has content. Read the field below as the
-- weakened statement it is, not as evidence of immutability.
--
-- The four that remain are genuine adapter trust: (1) name encoding,
-- (2) that the host payload IS the registry, (5) that host flags mean
-- what we read, and (7) that hidden bodies were captured.
--
-- M2c UPDATE. `Core.AdapterChecks` then read the ACTUAL producer and
-- found that (5) and (7) are not silent assumptions at all: they are
-- FAIL-CLOSED CHECKS `Cure.Core.ProofSnapshot` already performs
-- (`proof_snapshot.ex:94` and `:97`). Modelling those checks as a
-- `Validated` payload makes both obligations theorems, and gives (1) a
-- proved INTERNED form. So:
--
--   (5) flags-uninterpreted     -- `AdapterChecks.flags-uninterpreted`
--   (7) hidden-bodies-captured  -- `AdapterChecks.hidden-bodies-captured`
--   (1) name-encoding           -- `AdapterChecks.name-encoding-interned`
--                                  (PARTIAL: names are interned as table
--                                  indices, because a character-faithful
--                                  String round-trip is unavailable
--                                  without the `Data.String.Unsafe`
--                                  postulate this development refuses)
--
-- Only (2) remains, and it is not provable at all: "the host payload IS
-- the registry" is a fact about Elixir state that no Agda type can
-- witness. A field claiming it would be exactly the unproved assumption
-- this milestone exists to remove.
------------------------------------------------------------------------

record Ledger : Set where
  constructor ledger
  field
    proved : List String
    assumed : List String
open Ledger public

-- The ledger for the M2a deliverable.
m2a-ledger : Ledger
m2a-ledger = ledger
  ( "host key lookup is the formal first-match lookup (host-key-agrees)"
  ∷ "a duplicate-free table resolves each key to its unique binding (unique-lookup-stable)"
  ∷ "a duplicate key makes resolution order-dependent (duplicate-first-wins, duplicate-second-wins)"
  ∷ "a duplicate table fails the check (duplicate-not-unique)"
  ∷ "an alias cannot shadow a present key (alias-cannot-shadow)"
  ∷ "an alias to an absent target yields nothing (alias-absent-target)"
  ∷ "a table passing the check resolves every present key (checked-resolves)"
  ∷ [] )
  ( "string spellings correspond to formal Names (name-encoding)"
  ∷ "the adapter's flattening preserves the host binding set (extracted)"
  ∷ "the host collection is duplicate-free and the adapter enforces it (duplicates-rejected)"
  ∷ "the adapter keeps aliases out of the key table (aliases-separate)"
  ∷ "certification flags are transported without interpretation (flags-uninterpreted)"
  ∷ "constructor declaration order is preserved (order-preserved)"
  ∷ "uncertified raw bodies are captured, not filtered (hidden-bodies-captured)"
  ∷ "one immutable signature serves every stage (signature-immutable)"
  ∷ [] )

------------------------------------------------------------------------
-- Non-vacuity of the ledger itself.
--
-- A ledger with no entries would make the split meaningless. Both
-- sides are nonempty.
------------------------------------------------------------------------

proved-nonempty : ¬ (proved m2a-ledger ≡ [])
proved-nonempty ()

assumed-nonempty : ¬ (assumed m2a-ledger ≡ [])
assumed-nonempty ()
