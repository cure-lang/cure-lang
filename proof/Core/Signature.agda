------------------------------------------------------------------------
-- Inductive family declarations and the global signature.
--
-- Faithful to `Cure.Core.Inductive` (lib/cure/core/inductive.ex). A family
-- has a parameter telescope, an index telescope, a universe level, and a
-- list of constructors. Each constructor has an argument telescope and a
-- list of result indices.
--
-- The kernel enforces two guards at declaration time (docs/SOUNDNESS.md
-- §3.1, §3.3):
--
--   * UNIVERSE CHECK — a constructor field cannot live in a bigger universe
--     than the family itself.
--   * STRICT POSITIVITY — the family name never occurs to the left of an
--     arrow in any of its own constructors' field types.
--
-- Both are side conditions of the soundness theorem. We record them as
-- fields of the family record so a later slice can prove that a declared
-- signature satisfies them; for now they are carried as data.
------------------------------------------------------------------------
module Core.Signature where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.String using (String; _==_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax

------------------------------------------------------------------------
-- Telescopes: a list of named types, each possibly depending on earlier
-- entries (a genuine dependent telescope).
------------------------------------------------------------------------

Telescope : Set
Telescope = List (Name × Term)

------------------------------------------------------------------------
-- Constructor declaration
------------------------------------------------------------------------

record Ctor : Set where
  field
    ctor-name     : Name
    ctor-args     : Telescope   -- the argument telescope
    ctor-indices  : List Term   -- result indices (terms over the telescope)
    ctor-params   : List Term   -- result parameters (uniform, = family params)

open Ctor public

------------------------------------------------------------------------
-- Family declaration
------------------------------------------------------------------------

record Family : Set where
  field
    fam-name     : Name
    fam-params   : Telescope
    fam-indices  : Telescope
    fam-level    : Level
    fam-ctors    : List Ctor
    -- The two declaration-time guards, carried as data.
    -- `universe-ok`: every field type's level ≤ fam-level.
    -- `positive`   : the family name never occurs to the left of an arrow.
    universe-ok  : Bool
    positive     : Bool

open Family public

------------------------------------------------------------------------
-- The global signature: families, constructors, and certified globals.
--
-- We reuse `Core.Reduction.Signature` for the δ-table (global bodies and
-- declared types) and add the inductive environment here.
------------------------------------------------------------------------

record IndEnv : Set where
  field
    families : List Family
    -- Builtin family identities, e.g. `:nat`, `:bool`, `:eq`, `:sigma`.
    builtins : Name → Maybe Name

open IndEnv public

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

findFamily : Name → List Family → Maybe Family
findFamily n [] = nothing
findFamily n (f ∷ fs) with n == fam-name f
... | true  = just f
... | false = findFamily n fs

-- Find a constructor within a list of constructors.
findCtorIn : Name → List Ctor → Maybe Ctor
findCtorIn n [] = nothing
findCtorIn n (c ∷ cs) with n == ctor-name c
... | true  = just c
... | false = findCtorIn n cs

-- Find a constructor (and its owning family) by name across all families.
findCtor : Name → List Family → Maybe (Family × Ctor)
findCtor n [] = nothing
findCtor n (f ∷ fs) with findCtorIn n (fam-ctors f)
... | just c = just (f , c)
... | nothing = findCtor n fs

------------------------------------------------------------------------
-- Strict positivity (nested), mirroring `Inductive.positive?/2`.
--
-- `occursNegative n t` — does `n` occur to the LEFT of an arrow in `t`?
-- `occursPositive n t` — does `n` occur anywhere (for the nested walk)?
--
-- The nested walk descends into other families' constructors when a field
-- mentions them, so a negative occurrence smuggled through a wrapper is
-- also rejected (docs/KERNEL.md "Strict positivity").
------------------------------------------------------------------------

-- A family name occurs at all in a term.
mutual
  occursInBranches : Name → List (Name × ℕ × Term) → Bool
  occursInBranches n [] = false
  occursInBranches n (x ∷ xs) = occursInBranch n x ∨ occursInBranches n xs

  occursInBranch : Name → (Name × ℕ × Term) → Bool
  occursInBranch n (cn , ar , b) = occursIn n b

  occursInTerms : Name → List Term → Bool
  occursInTerms n [] = false
  occursInTerms n (x ∷ xs) = occursIn n x ∨ occursInTerms n xs

  occursIn : Name → Term → Bool
  occursIn n (tm-type l) = false
  occursIn n (tm-var k) = false
  occursIn n (tm-pi g d c) = occursIn n d ∨ occursIn n c
  occursIn n (tm-lam g d b) = occursIn n d ∨ occursIn n b
  occursIn n (tm-let g ty v b) = occursIn n ty ∨ occursIn n v ∨ occursIn n b
  occursIn n (tm-app f a) = occursIn n f ∨ occursIn n a
  occursIn n (tm-data m ps is) = (n == m) ∨ occursInTerms n ps ∨ occursInTerms n is
  occursIn n (tm-ctor m args) = occursInTerms n args
  occursIn n (tm-case s m brs) = occursIn n s ∨ occursIn n m ∨ occursInBranches n brs
  occursIn n (tm-global m) = false
  occursIn n (tm-int_type) = false
  occursIn n (tm-int_lit k) = false
  occursIn n (tm-nat_lit k) = false
  occursIn n (tm-bounded_lit k) = false
  occursIn n (tm-float_type) = false
  occursIn n (tm-float_lit) = false
  occursIn n (tm-binary_type) = false
  occursIn n (tm-atom_type) = false
  occursIn n (tm-atom_lit m) = false
  occursIn n (tm-effect_type t) = occursIn n t
  occursIn n (tm-effect_pure t) = occursIn n t
  occursIn n (tm-effect_bind e k) = occursIn n e ∨ occursIn n k
  occursIn n (tm-hole m) = false
  occursIn n (tm-absurd) = false

-- `n` occurs to the LEFT of an arrow: in the domain of a Π, or anywhere
-- inside a domain that is itself a Π-chain. This is the negative position.
occursNegative : Name → Term → Bool
occursNegative n (tm-pi g d c) = occursIn n d ∨ occursNegative n c
occursNegative n (tm-lam g d b) = occursNegative n b
occursNegative n (tm-let g ty v b) = occursNegative n b
occursNegative n (tm-app f a) = occursNegative n f ∨ occursNegative n a
occursNegative n (tm-case s m brs) = occursNegative n s ∨ occursNegative n m
occursNegative n (tm-effect_type t) = occursNegative n t
occursNegative n (tm-effect_pure t) = occursNegative n t
occursNegative n (tm-effect_bind e k) = occursNegative n e ∨ occursNegative n k
occursNegative n t = false
