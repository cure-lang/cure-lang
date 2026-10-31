------------------------------------------------------------------------
-- Inhabitation and negative controls for `Core.HostTable`.
--
-- The general theorems in `Core.HostTable` are quantified over
-- arbitrary host tables. This module fixes CONCRETE tables and
-- exercises every case, so the quantified statements are known to be
-- non-vacuous and the negative controls are known to fail for the
-- intended reason rather than incidentally.
--
-- The concrete names mirror the executable fixture's owner-qualified
-- spelling (`Boundary#Packed`, `Boundary#Pack`) so the model is
-- recognisably about the real registry, but nothing here claims
-- correspondence with the Elixir implementation. That boundary is
-- recorded in `Core.RepresentationBoundary`.
------------------------------------------------------------------------
module Proof.HostTableExamples where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Core.Syntax using (Name)
open import Core.HostTable
import Core.CanonicalSnapshot as S

------------------------------------------------------------------------
-- A concrete registry presented as a host table.
--
-- Two families and two globals, with the families listed in one order
-- and the globals in another. `ℕ`-valued payloads stand in for the
-- formal entries: this module is about RESOLUTION, not about what the
-- entries contain, so the payload type is irrelevant and kept small.
------------------------------------------------------------------------

packed : String
packed = "Boundary#Packed"

pack : String
pack = "Boundary#Pack"

answer : String
answer = "Boundary#answer"

held : String
held = "Boundary#held"

-- Families first, then globals, in the order an adapter might emit.
registry : HostTable ℕ
registry = host-table
  ( (packed , 0) ∷ (pack , 1) ∷ (answer , 2) ∷ (held , 3) ∷ [] )
  []

-- The same bindings, presented in a DIFFERENT order. Because the
-- table is duplicate-free, every lookup must agree.
reordered : HostTable ℕ
reordered = host-table
  ( (held , 3) ∷ (answer , 2) ∷ (pack , 1) ∷ (packed , 0) ∷ [] )
  []

-- `Fresh` evidence for a key against a list, given a refutation of the
-- key's equality with every member's name. Written once so the concrete
-- tables below stay readable.
fresh-all : ∀ {A} {key : Name} {bindings : List (Name × A)}
  → (∀ {name value} → (name , value) ∈ bindings → key ≢ name)
  → S.Fresh key bindings
fresh-all {bindings = []} refute = S.fresh[]
fresh-all {bindings = (name , value) ∷ rest} refute =
  S.fresh∷ (refute (here refl)) (fresh-all (λ member → refute (there member)))

------------------------------------------------------------------------
-- Positive results.
------------------------------------------------------------------------

-- The table is duplicate-free. Each `Fresh` obligation is discharged by
-- refuting the concrete name equation, which Agda decides because the
-- keys are literal strings.
registry-unique : Unique (bindings registry)
registry-unique =
  S.unique∷ (fresh-all {key = packed} packed-absent)
    (S.unique∷ (fresh-all {key = pack} pack-absent)
      (S.unique∷ (fresh-all {key = answer} answer-absent)
        (S.unique∷ S.fresh[] S.unique[])))
  where
  packed-absent : ∀ {name value} → (name , value) ∈ (pack , 1) ∷ (answer , 2) ∷ (held , 3) ∷ []
    → packed ≢ name
  packed-absent (here refl) = λ ()
  packed-absent (there (here refl)) = λ ()
  packed-absent (there (there (here refl))) = λ ()

  pack-absent : ∀ {name value} → (name , value) ∈ (answer , 2) ∷ (held , 3) ∷ []
    → pack ≢ name
  pack-absent (here refl) = λ ()
  pack-absent (there (here refl)) = λ ()

  answer-absent : ∀ {name value} → (name , value) ∈ (held , 3) ∷ []
    → answer ≢ name
  answer-absent (here refl) = λ ()

-- The decidable check agrees with the constructive evidence.
registry-check : check-table registry ≡ yes registry-unique
registry-check = refl

-- A present key resolves to its binding, through the host's own
-- resolution rather than the formal lookup.
packed-resolves : host-lookup packed registry ≡ just 0
packed-resolves = checked-resolves {A = ℕ} {table = registry} {value = 0} registry-unique (here refl)

held-resolves : host-lookup held registry ≡ just 3
held-resolves = checked-resolves {A = ℕ} {table = registry} {value = 3} registry-unique (there (there (there (here refl))))

-- An absent key resolves to nothing.
absent-resolves : host-lookup "Boundary#absent" registry ≡ nothing
absent-resolves = refl

-- THE ORDER-INSENSITIVITY PAYOFF: the reordered presentation agrees
-- on every key we name. This is the property the executable's
-- unordered map relies on.
packed-order-insensitive : host-lookup packed reordered ≡ host-lookup packed registry
packed-order-insensitive = refl

held-order-insensitive : host-lookup held reordered ≡ host-lookup held registry
held-order-insensitive = refl

-- Stated generally for this pair: the two presentations agree on the
-- keys that are present, via the uniqueness theorem rather than by
-- enumerating them.
reordered-unique : Unique (bindings reordered)
reordered-unique =
  S.unique∷ (fresh-all {key = held} held-absent)
    (S.unique∷ (fresh-all {key = answer} answer-absent)
      (S.unique∷ (fresh-all {key = pack} pack-absent)
        (S.unique∷ S.fresh[] S.unique[])))
  where
  held-absent : ∀ {name value} → (name , value) ∈ (answer , 2) ∷ (pack , 1) ∷ (packed , 0) ∷ []
    → held ≢ name
  held-absent (here refl) = λ ()
  held-absent (there (here refl)) = λ ()
  held-absent (there (there (here refl))) = λ ()

  answer-absent : ∀ {name value} → (name , value) ∈ (pack , 1) ∷ (packed , 0) ∷ []
    → answer ≢ name
  answer-absent (here refl) = λ ()
  answer-absent (there (here refl)) = λ ()

  pack-absent : ∀ {name value} → (name , value) ∈ (packed , 0) ∷ []
    → pack ≢ name
  pack-absent (here refl) = λ ()

------------------------------------------------------------------------
-- Negative controls.
------------------------------------------------------------------------

-- A table with a duplicate key is REJECTED by the check. This is the
-- executable's "no duplicate keys" invariant, and it is what makes the
-- order-insensitivity theorem above applicable.
duplicated : HostTable ℕ
duplicated = host-table ((packed , 0) ∷ (packed , 9) ∷ []) []

duplicated-rejected : check-table duplicated ≡ no (duplicate-not-unique packed 0 9)
duplicated-rejected = refl

-- And the rejection is not cosmetic: the two presentations of the
-- duplicate resolve DIFFERENTLY, so an adapter that silently kept both
-- would change resolution.
duplicate-disagrees :
    S.lookup packed (duplicate-pair packed 0 9)
  ≢ S.lookup packed ((packed , 9) ∷ (packed , 0) ∷ [])
duplicate-disagrees equal with equal
... | ()

-- An alias cannot shadow a present key: `packed` is present, so an
-- alias redirecting `packed` elsewhere is ignored.
shadowing : HostTable ℕ
shadowing = host-table ((packed , 0) ∷ (pack , 1) ∷ []) ((packed , pack) ∷ [])

alias-ignored : host-lookup packed shadowing ≡ just 0
alias-ignored = alias-cannot-shadow packed shadowing refl

-- An alias whose target is absent yields nothing rather than a
-- fabricated binding.
dangling : HostTable ℕ
dangling = host-table ((pack , 1) ∷ []) (("Boundary#alias" , "Boundary#missing") ∷ [])

dangling-absent : host-lookup "Boundary#alias" dangling ≡ nothing
dangling-absent = refl

-- A key present only via an alias DOES resolve, but through the alias
-- target, so the indirection is observable rather than transparent.
redirected : HostTable ℕ
redirected = host-table ((pack , 1) ∷ []) (("Boundary#alias" , pack) ∷ [])

redirected-resolves : host-lookup "Boundary#alias" redirected ≡ just 1
redirected-resolves = refl

------------------------------------------------------------------------
-- Agreement with the formal view, on the concrete tables.
--
-- `host-key-agrees` is general; we record its instance so a reader can
-- see the host and formal lookups really are the same function here.
------------------------------------------------------------------------

formal-agrees : S.lookup packed (bindings registry) ≡ just 0
formal-agrees = S.member-lookup registry-unique (here refl)

host-matches-formal : host-key packed (bindings registry) ≡ S.lookup packed (bindings registry)
host-matches-formal = host-key-agrees packed (bindings registry)
