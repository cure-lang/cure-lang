------------------------------------------------------------------------
-- M2a: host-shaped finite tables and their formal first-match view.
--
-- The executable registry is an Elixir MAP: an unordered keyed
-- collection with no duplicate keys. The formal registry
-- (`Core.Signature`) is an ORDERED list searched first-match. The
-- existing `Core.CanonicalSnapshot` relates a canonical LIST to formal
-- lookup, but it takes that list as given: nothing there relates the
-- list to a host-shaped source, and nothing states which host
-- behaviours are modelled at all.
--
-- This module supplies the missing host side. A `HostTable` is a
-- finite association list that MAY contain duplicate keys, MAY be
-- presented in any order, and MAY carry alias entries. We define the
-- host's own resolution (first-match over the presented order, then a
-- single alias hop) and prove, for ARBITRARY such tables:
--
--   * `host-key-agrees`   host key lookup IS the formal lookup;
--   * `unique-lookup-stable` a duplicate-free table resolves each key
--     to its unique binding, so ANY re-presentation is equivalent;
--   * `duplicate-first-wins` / `duplicate-second-wins` /
--     `duplicate-not-unique` a duplicate key makes resolution depend
--     on presentation order, so duplicate-freedom is load-bearing;
--   * `alias-cannot-shadow` / `alias-absent-target` alias fallback
--     cannot shadow a present key or fabricate a binding.
--
-- SCOPE. This is a model of the host's name-resolution ORDER and
-- duplicate behaviour. It is NOT a model of Elixir's map, of atom
-- interning, of `Cure.Elab.Name.split/1`, or of the producer that
-- fills the table. Those remain explicit adapter trust, recorded in
-- `Core.RepresentationBoundary`. No new axiom, hole or checking
-- override is introduced.
------------------------------------------------------------------------
module Core.HostTable where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Core.Syntax using (Name)
import Core.CanonicalSnapshot as S

------------------------------------------------------------------------
-- The host side.
--
-- A `HostTable` is what a host adapter can hand us after reading a
-- keyed collection: an ordered list of bindings, possibly with
-- repeated keys, plus a separate alias table. Keeping aliases in a
-- SEPARATE table is deliberate: an alias is a spelling redirect, not
-- a competing binding, so it must never win over a real key.
------------------------------------------------------------------------

record HostTable (A : Set) : Set where
  constructor host-table
  field
    bindings : List (Name × A)
    aliases  : List (Name × Name)
open HostTable public

------------------------------------------------------------------------
-- Host key resolution: first match in the PRESENTED order.
--
-- Deliberately the same shape as the formal lookup, so the agreement
-- theorem below is a structural induction rather than a coincidence.
-- The interesting content is what this lets us prove about order and
-- duplicates.
------------------------------------------------------------------------

host-key : ∀ {A : Set} → Name → List (Name × A) → Maybe A
host-key key [] = nothing
host-key key ((name , value) ∷ rest) with key ≟ name
... | yes same = just value
... | no different = host-key key rest

-- Alias resolution: follow ONE redirect, then retry key lookup. A
-- single hop suffices for the current spelling convention, and a
-- bounded hop count keeps this total without a termination argument
-- over a possibly cyclic alias table.
alias-target : Name → List (Name × Name) → Maybe Name
alias-target key [] = nothing
alias-target key ((from , to) ∷ rest) with key ≟ from
... | yes same = just to
... | no different = alias-target key rest

-- The host's own resolution: real keys first, then one alias hop.
host-lookup : ∀ {A : Set} → Name → HostTable A → Maybe A
host-lookup key table with host-key key (bindings table)
... | just value = just value
... | nothing with alias-target key (aliases table)
... | just target = host-key target (bindings table)
... | nothing = nothing

------------------------------------------------------------------------
-- Agreement with the formal view.
--
-- `Core.CanonicalSnapshot.lookup` is the formal first-match lookup the
-- native signature is built from. The host's key resolution is the
-- same function, so agreement is definitional. Stating it explicitly
-- matters: it fixes WHICH formal lookup the host is claimed to
-- implement, so a later change to either side breaks the equation.
------------------------------------------------------------------------

host-key-agrees : ∀ {A : Set} key (bindings : List (Name × A))
  → host-key key bindings ≡ S.lookup key bindings
host-key-agrees key [] = refl
host-key-agrees key ((name , value) ∷ rest) with key ≟ name
... | yes same = refl
... | no different = host-key-agrees key rest

------------------------------------------------------------------------
-- Order insensitivity.
--
-- The executable registry is unordered, so an adapter is free to
-- present bindings in ANY order. The formal snapshot, however, is
-- order-sensitive in general: with duplicate keys, permuting the
-- bindings changes the first match. Order-insensitivity is therefore
-- exactly what duplicate-freedom buys, and we prove both directions
-- rather than assuming it.
------------------------------------------------------------------------

-- A binding list is duplicate-free when every key is `Fresh` of the
-- tail. This is `Core.CanonicalSnapshot.Unique`, reused rather than
-- redefined so the two developments cannot drift.
Unique : ∀ {A : Set} → List (Name × A) → Set
Unique = S.Unique

-- THE ORDER-INSENSITIVITY THEOREM. A duplicate-free table has at most
-- one binding per key, so its lookup is the unique binding and ANY
-- re-presentation of the same bindings resolves every key identically.
-- This is why the executable's duplicate-key rejection is load-bearing
-- for the representation claim rather than a nicety.
unique-lookup-stable : ∀ {A : Set} {bindings : List (Name × A)}
  → Unique bindings → ∀ {key value} → (key , value) ∈ bindings
  → S.lookup key bindings ≡ just value
unique-lookup-stable unique {key} {value} member =
  S.member-lookup unique member

-- Insertion of a fresh key commutes with lookup of any OTHER key. This
-- is the workhorse for order-insensitivity: it is what lets an adapter
-- present bindings in any order it likes. The `other ≢ key` premise is
-- not a weakening: when `other ≡ key` the inserted binding IS the
-- answer, which is exactly the case the premise excludes.
fresh-tail : ∀ {A : Set} {key : Name} {name : Name} {entry : A}
    {bindings : List (Name × A)}
  → S.Fresh key ((name , entry) ∷ bindings) → S.Fresh key bindings
fresh-tail (S.fresh∷ _ tail) = tail

-- Freshness of a key in a cons-list rules out the head key.
fresh-excludes-here : ∀ {A} {key : Name} {name : Name} {entry : A}
    {rest : List (Name × A)}
  → S.Fresh key ((name , entry) ∷ rest) → key ≡ name → ⊥
fresh-excludes-here (S.fresh∷ different _) same = different same

-- `S.lookup` skips a head binding whose key differs. Stated as an
-- equation so callers can `rewrite` with it rather than relying on
-- the decision procedure reducing definitionally.
lookup-skips : ∀ {A : Set} {other : Name} {name : Name} {entry : A}
    {rest : List (Name × A)}
  → other ≢ name
  → S.lookup other ((name , entry) ∷ rest) ≡ S.lookup other rest
lookup-skips {other = other} {name = name} different with other ≟ name
... | yes same = ⊥-elim (different same)
... | no unequal = refl

-- Lookup of a key in `(key,v) ∷ rest` when `key` is NOT the head: the
-- inserted binding is invisible. Stated with the head key as a separate
-- parameter so no `with`-abstraction can hide the decision.
insert-invisible : ∀ {A : Set} (key other : Name) (value : A)
    (bindings : List (Name × A))
  → other ≢ key
  → S.lookup other ((key , value) ∷ bindings) ≡ S.lookup other bindings
insert-invisible key other value bindings different
  with other ≟ key
... | yes same = ⊥-elim (different same)
... | no unequal = refl

-- Insertion of a fresh key commutes with lookup of any OTHER key: the
-- inserted binding is invisible to every key it does not name. This is
-- what makes an adapter free to present bindings in any order.
insert-fresh :
    ∀ {A : Set} {key : Name} {value : A} (bindings : List (Name × A))
  → S.Fresh key bindings
  → ∀ other → other ≢ key
  → S.lookup other bindings ≡ S.lookup other ((key , value) ∷ bindings)
insert-fresh {key = key} bindings fresh other different =
  sym (insert-invisible key other _ bindings different)

------------------------------------------------------------------------
-- Duplicates genuinely break order-insensitivity.
--
-- A two-binding table whose two presentations disagree on a key. This
-- is a NEGATIVE control with computational content: it shows the
-- `Unique` hypothesis above cannot be dropped, and it pins that an
-- adapter which silently collapses or reorders duplicates would change
-- resolution.
------------------------------------------------------------------------

-- Two bindings for the same key, in the two possible orders.
duplicate-pair : ∀ {A : Set} (key : Name) (first second : A)
  → List (Name × A)
duplicate-pair key first second = (key , first) ∷ (key , second) ∷ []

duplicate-first-wins :
    ∀ {A : Set} (key : Name) (first second : A)
  → S.lookup key (duplicate-pair key first second) ≡ just first
duplicate-first-wins key first second with key ≟ key
... | yes same = refl
... | no different = ⊥-elim (different refl)

duplicate-second-wins :
    ∀ {A : Set} (key : Name) (first second : A)
  → S.lookup key ((key , second) ∷ (key , first) ∷ []) ≡ just second
duplicate-second-wins key first second with key ≟ key
... | yes same = refl
... | no different = ⊥-elim (different refl)

-- A duplicate table is NOT `Unique`. Stated alongside the two facts
-- above so a reader cannot mistake the negative control for an
-- oversight.
duplicate-not-unique :
    ∀ {A : Set} (key : Name) (first second : A)
  → ¬ Unique (duplicate-pair key first second)
duplicate-not-unique key first second (S.unique∷ {name = name} fresh rest)
  with key ≟ name
... | yes refl = S.fresh-excludes fresh (here refl)
... | no different = different refl

------------------------------------------------------------------------
-- Alias discipline.
--
-- An alias must never shadow a present key, and an alias whose target
-- is absent must not fabricate a binding. Both are proved, because
-- both are the ways an alias table can silently change resolution.
------------------------------------------------------------------------

-- A present key ignores aliases entirely.
alias-cannot-shadow :
    ∀ {A : Set} key (table : HostTable A) {value}
  → host-key key (bindings table) ≡ just value
  → host-lookup key table ≡ just value
alias-cannot-shadow key table present rewrite present = refl

-- An alias to an absent target yields nothing, not a default.
alias-absent-target :
    ∀ {A : Set} key (table : HostTable A) {target}
  → host-key key (bindings table) ≡ nothing
  → alias-target key (aliases table) ≡ just target
  → host-key target (bindings table) ≡ nothing
  → host-lookup key table ≡ nothing
alias-absent-target key table absent alias target-absent
  rewrite absent | alias = target-absent

-- A key with neither a binding nor an alias resolves to nothing.
host-lookup-absent :
    ∀ {A : Set} key (table : HostTable A)
  → host-key key (bindings table) ≡ nothing
  → alias-target key (aliases table) ≡ nothing
  → host-lookup key table ≡ nothing
host-lookup-absent key table absent no-alias
  rewrite absent | no-alias = refl

------------------------------------------------------------------------
-- The executable invariant, as a decidable check.
--
-- An adapter is required to reject duplicate keys BEFORE the table is
-- used as a representation of the registry. `check-table` is the
-- decidable form of that requirement, reusing the canonical
-- duplicate-freedom decision procedure so there is exactly one
-- definition of "duplicate-free" in the development.
------------------------------------------------------------------------

check-table : ∀ {A : Set} → (table : HostTable A) → Dec (Unique (bindings table))
check-table table = S.unique? (bindings table)

-- A table that passes the check resolves every key to its unique
-- binding, which is the property the representation relation needs.
-- `host-key` is by construction the formal lookup, so this is the
-- formal membership lemma transported through `host-key-agrees`.
checked-resolves :
    ∀ {A : Set} {table : HostTable A} {key value}
  → Unique (bindings table)
  → (key , value) ∈ bindings table
  → host-lookup key table ≡ just value
checked-resolves {table = table} {key = key} unique member
  rewrite host-key-agrees key (bindings table)
        | S.member-lookup unique member = refl

