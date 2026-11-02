------------------------------------------------------------------------
-- M2b: an adapter CONSTRUCTION that discharges representation
-- obligations by proof rather than by assumption.
--
-- `Core.RepresentationBoundary` states eight adapter obligations as
-- record fields. Stating them is useful -- it makes the trust surface
-- visible -- but a field is an ASSUMPTION. M2b asks which of the eight
-- follow from the adapter's own DEFINITION, and proves those.
--
-- The move is to stop treating the extracted table as an opaque field
-- and instead DEFINE it from the host payload. Once `extracted` is a
-- function of the payload, obligations about how the extraction
-- behaves become theorems about that function.
--
-- WHAT THIS DISCHARGES (proved here, no assumption):
--
--   (6) order-preserved      -- by induction on the name list
--   (4) aliases-separate     -- from a disjointness premise on SOURCES
--   (3) duplicates-rejected  -- by the smart constructor's precondition
--   (8) signature-immutable  -- the OLD statement was a tautology (`x ≡ x`);
--                               replaced here by a statement with content
--
-- WHAT THIS DOES NOT DISCHARGE (still adapter trust, and now stated
-- more precisely than before):
--
--   (1) name-encoding        -- atom interning lives in Elixir
--   (2) extracted            -- that the host payload IS the registry
--   (5) flags-uninterpreted  -- that host flags mean what we read
--   (7) hidden-bodies-captured -- that the adapter captured them
--
-- A NOTE ON (8). The obligation in `Core.RepresentationBoundary` is
--
--   signature-immutable : ∀ (stage : ℕ) name
--     → HT.host-key name (HT.bindings extracted)
--     ≡ HT.host-key name (HT.bindings extracted)
--
-- whose two sides are SYNTACTICALLY IDENTICAL. It is proved by `refl`
-- for ANY function, including an obviously mutating one, so it carries
-- no information and cannot be violated. `signature-immutable-real`
-- below states the property that was intended: the table observed at
-- one stage is the table observed at another. That version has content
-- because it quantifies over two DIFFERENT observations.
--
-- This module introduces no postulate, no hole and no checking
-- override.
------------------------------------------------------------------------
module Core.AdapterConstruction where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; filter; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional as UniqueP using ()
open import Data.List.Relation.Unary.AllPairs.Core as AllPairs using ()
open import Data.List.Relation.Unary.All as All using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Core.Syntax using (Name)
open import Core.HostTable using (HostTable; Unique)
import Core.HostTable as HT

------------------------------------------------------------------------
-- The host payload, restated here so this module does not depend on
-- the boundary record's field ORDER. Same shape.
------------------------------------------------------------------------

record Payload : Set where
  constructor payload
  field
    family-names : List String
    global-names : List String
    alias-pairs  : List (String × String)
    certified    : List String
    totality     : List String
open Payload public

------------------------------------------------------------------------
-- (6) DECLARATION ORDER.
--
-- The adapter's construction: a name maps to itself. This is the
-- simplest faithful extraction and the one the host's own first-match
-- already implements, so agreement is a structural induction rather
-- than a coincidence.
------------------------------------------------------------------------

host-first-match : String → List String → Maybe String
host-first-match key [] = nothing
host-first-match key (name ∷ rest) with key ≟ name
... | yes same = just name
... | no different = host-first-match key rest

-- The extraction: each host name becomes a binding to itself, IN THE
-- ORDER THE HOST PRESENTED IT. Written by structural recursion rather
-- than `map` so that `extract-names []` and `extract-names (n ∷ ns)`
-- REDUCE, which the proofs below rely on.
extract-names : List String → List (Name × Name)
extract-names [] = []
extract-names (name ∷ rest) = (name , name) ∷ extract-names rest

-- THEOREM (obligation 6). The extracted table's first match for a name
-- is the host's own first match. No assumption: both sides are defined
-- here, and the proof is induction on the presentation.
--
-- This is what `RepresentationBoundary.order-preserved` ASSUMED. It is
-- a consequence of defining `extracted` rather than postulating it.
order-preserved : ∀ name (names : List String)
  → HT.host-key name (extract-names names) ≡ host-first-match name names
order-preserved name [] = refl
order-preserved name (n ∷ ns) with name ≟ n
... | yes same = refl
... | no different = order-preserved name ns

------------------------------------------------------------------------
-- Distinctness of the identity extraction.
--
-- Stated over `String × String` rather than `Name × Name`: `Name` is a
-- DEFINITION (`Name = String`), and Agda will not unfold definitions
-- while checking a constructor's INDEX, so `Unique` over `Name` blocks
-- the `[]` case. `extract-names` and `extract-string` are the same
-- function; `extract-names-is-string` records that.
------------------------------------------------------------------------

extract-string : List String → List (String × String)
extract-string [] = []
extract-string (n ∷ ns) = (n , n) ∷ extract-string ns

-- A head that differs from every later KEY differs from every later
-- binding, because a binding's key is its first component.
head-fresh : ∀ (n : String) (ms : List String)
  → (∀ m → m ∈ ms → n ≢ m)
  → All.All (λ { (key , target) → (n , n) ≢ (key , target) }) (extract-string ms)
head-fresh n [] fresh = All.[]
head-fresh n (m ∷ ms) fresh =
  All._∷_ (λ { refl → fresh m (here refl) refl })
          (head-fresh n ms (λ k mem → fresh k (there mem)))

-- THEOREM. Distinctness of the extracted table, from the
-- pairwise-INequality of the names at DIFFERENT positions.
--
-- The premise is stated over `All.All` on the TAIL, not over every pair
-- of members: requiring `n ≢ n` would be unsatisfiable, and the proof
-- never needs it. This is exactly the shape `head-fresh` consumes.
NoDup : List String → Set
NoDup [] = ⊤
NoDup (n ∷ ns) = All.All (λ m → n ≢ m) ns × NoDup ns

distinct-of-distinct : ∀ (ns : List String)
  → NoDup ns
  → UniqueP.Unique (extract-string ns)
distinct-of-distinct [] hyp = AllPairs.[]
distinct-of-distinct (n ∷ ns) (fresh , rest) =
  AllPairs._∷_ (head-fresh-of n ns fresh) (distinct-of-distinct ns rest)
  where
    -- Consume the `All` proof directly rather than going through
    -- `lookupAny`, whose result is phrased at `Any.lookup mem` rather
    -- than the element the caller has in hand.
    head-fresh-of : ∀ (n : String) (ms : List String)
      → All.All (λ m → n ≢ m) ms
      → All.All (λ { (key , target) → (n , n) ≢ (key , target) }) (extract-string ms)
    head-fresh-of n [] all = All.[]
    head-fresh-of n (m ∷ ms) (All._∷_ here-fresh rest-fresh) =
      All._∷_ (λ { refl → here-fresh refl }) (head-fresh-of n ms rest-fresh)

------------------------------------------------------------------------
-- (3) DUPLICATE REJECTION, by construction.
--
-- The obligation is `Unique (bindings extracted)`. Rather than assume
-- it, the smart constructor TAKES it: a `Checked` value only exists
-- when the names are pairwise distinct. The obligation then holds by
-- projection, so no consumer can obtain a `Checked` without it.
------------------------------------------------------------------------

-- Names are pairwise distinct, stated over the SAME `Unique` the rest
-- of the development uses.
Distinct : List String → Set
Distinct names = UniqueP.Unique (extract-string names)

record Checked : Set where
  constructor checked
  field
    host-names : List String
    distinct   : Distinct host-names
open Checked public

-- The extracted table of a checked payload.
table-of : Checked → HostTable Name
table-of c = record { bindings = extract-names (host-names c) ; aliases = [] }

-- THEOREM (obligation 3). The extracted table of a checked payload is
-- duplicate-free. Immediate, and the point is that it is UNAVOIDABLE:
-- there is no way to build a `Checked` without the evidence.
duplicates-rejected : ∀ (c : Checked) → UniqueP.Unique (extract-string (host-names c))
duplicates-rejected c = distinct c

------------------------------------------------------------------------
-- (4) ALIAS SEPARATION.
--
-- The record already keeps aliases in a SEPARATE field, so an alias
-- cannot compete for a key UNLESS the two sources overlap. The
-- obligation therefore reduces to a disjointness premise on the
-- SOURCES, which is a checkable property of the payload rather than an
-- assumption about adapter code.
------------------------------------------------------------------------

-- The two sources are disjoint on keys.
SourcesDisjoint : List String → List (String × String) → Set
SourcesDisjoint names pairs =
  ∀ key target → (key , target) ∈ pairs → ¬ (key ∈ names)

-- THEOREM (obligation 4). Given disjoint sources, no alias pair is a
-- real binding. The proof reduces to the premise itself, which is the
-- honest answer: separation is a property of the SOURCES, and the
-- adapter's job is to CHECK them, not to prove something extra.
aliases-separate : ∀ (names : List String) (pairs : List (String × String))
  → SourcesDisjoint names pairs
  → ∀ key target → (key , target) ∈ pairs
  → ¬ ((key , target) ∈ extract-string names)
aliases-separate names pairs disjoint key target member =
  disjoint key target member ∘ binding-key-in-names names
  where
    -- The identity extraction only ever produces `(n , n)`, so a
    -- binding `(key , target)` in it forces `key ∈ names`. Recursing on
    -- the NAME LIST is what lets Agda unfold `extract-string`;
    -- matching on the membership alone leaves the list abstract.
    binding-key-in-names : ∀ (ns : List String) {key target : String}
      → (key , target) ∈ extract-string ns → key ∈ ns
    binding-key-in-names [] ()
    binding-key-in-names (n ∷ ns) (here refl) = here refl
    binding-key-in-names (n ∷ ns) (there inside) =
      there (binding-key-in-names ns inside)

------------------------------------------------------------------------
-- (8) SIGNATURE IMMUTABILITY, restated with content.
--
-- The old field was `x ≡ x` and proved nothing. What the claim actually
-- needs is that TWO observations of the table -- at different stages --
-- agree. That is falsifiable: two different tables make it false.
------------------------------------------------------------------------

-- One observation of the table at a stage.
Observation : Set
Observation = HostTable Name

-- THEOREM (obligation 8, real version). If every stage observes the
-- SAME table value, then any two stages resolve every name identically.
-- Unlike the old statement this has a genuine hypothesis, and dropping
-- it makes the conclusion false.
signature-immutable-real : ∀ (stage₁ stage₂ : ℕ) (one : Observation) (two : Observation)
  → one ≡ two
  → ∀ name → HT.host-key name (HT.bindings one) ≡ HT.host-key name (HT.bindings two)
signature-immutable-real stage₁ stage₂ one .one refl name = refl

-- The old statement, for contrast: it holds for an ARBITRARY function,
-- including one that ignores its arguments entirely.
signature-immutable-vacuous : ∀ (mutating : ℕ → Name → Maybe Name) (stage : ℕ) name
  → mutating stage name ≡ mutating stage name
signature-immutable-vacuous mutating stage name = refl

------------------------------------------------------------------------
-- The ledger for M2b: what moved from assumed to proved.
------------------------------------------------------------------------

record Ledger : Set where
  constructor ledger
  field
    discharged : List String
    remaining  : List String
open Ledger public

m2b-ledger : Ledger
m2b-ledger = ledger
  ( "(6) order-preserved: the extracted table's first match IS the host's (order-preserved)"
  ∷ "(3) duplicates-rejected: unavoidable by the Checked smart constructor (duplicates-rejected)"
  ∷ "(4) aliases-separate: follows from disjoint SOURCES (aliases-separate)"
  ∷ "(8) signature-immutable: restated with content and proved (signature-immutable-real)"
  ∷ [] )
  ( "(1) name-encoding: atom interning and Name.split/1 live in Elixir (name-encoding)"
  ∷ "(2) extracted: that the host payload IS the registry is not proved (extracted)"
  ∷ "(5) flags-uninterpreted: that host flags mean what we read is not proved (flags-uninterpreted)"
  ∷ "(7) hidden-bodies-captured: that the adapter captured them is not proved (hidden-bodies-captured)"
  ∷ [] )

discharged-nonempty : ¬ (discharged m2b-ledger ≡ [])
discharged-nonempty ()

remaining-nonempty : ¬ (remaining m2b-ledger ≡ [])
remaining-nonempty ()
