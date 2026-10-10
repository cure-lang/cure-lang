------------------------------------------------------------------------
-- Values: canonical forms and neutrals.
--
-- The kernel's notion of a value (`MetaCheck.canonical_head?/1`) includes
-- both introduction forms (λ, ctor, Π, Type, data, literals, effect
-- formers) and NEUTRALS (stuck computations). We split them:
--
--   * `Canonical` — the introduction forms, which cannot be stuck;
--   * `Neutral`   — a variable, global, hole, or eliminator stuck on a
--                   neutral;
--   * `Value`     — their union, recovering the kernel's notion.
--
-- The split matters: the canonical-form lemmas (Proof/CanonicalForms.agda)
-- are stated over `Canonical`, because "every value of Π type is a λ" is
-- FALSE for neutrals (a stuck application of Π type is a value).
------------------------------------------------------------------------
module Proof.Values where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.String using (String)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax

------------------------------------------------------------------------
-- Canonical (non-neutral) values
--
-- The introduction forms: the kernel's `MetaCheck.canonical_head?/1` minus
-- the neutral cases. A term in `Canonical` is a value that is NOT stuck on
-- a variable, global, or hole.
------------------------------------------------------------------------

data Canonical : Term → Set where
  c-type    : ∀ {l} → Canonical (tm-type l)
  c-pi      : ∀ {g d c} → Canonical (tm-pi g d c)
  c-lam     : ∀ {g d b} → Canonical (tm-lam g d b)
  c-data    : ∀ {n ps is} → Canonical (tm-data n ps is)
  c-ctor    : ∀ {n args} → Canonical (tm-ctor n args)
  c-int_type    : Canonical tm-int_type
  c-int_lit     : ∀ {k} → Canonical (tm-int_lit k)
  c-nat_lit     : ∀ {k} → Canonical (tm-nat_lit k)
  c-bounded_lit : ∀ {k} → Canonical (tm-bounded_lit k)
  c-float_type  : Canonical tm-float_type
  c-float_lit   : Canonical tm-float_lit
  c-binary_type : Canonical tm-binary_type
  c-atom_type   : Canonical tm-atom_type
  c-atom_lit    : ∀ {n} → Canonical (tm-atom_lit n)
  c-effect_type : ∀ {t} → Canonical (tm-effect_type t)
  c-effect_pure : ∀ {t} → Canonical (tm-effect_pure t)
  c-effect_bind : ∀ {e k} → Canonical (tm-effect_bind e k)

------------------------------------------------------------------------
-- Neutrals (stuck computations)
--
-- A neutral is a value whose head is a variable, a global, a hole, or an
-- eliminator stuck on a neutral. Neutrals are values, but they are the
-- "not yet canonical" ones.
------------------------------------------------------------------------

data Neutral : Term → Set where
  n-var    : ∀ {k} → Neutral (tm-var k)
  n-global : ∀ {n} → Neutral (tm-global n)
  n-hole   : ∀ {n} → Neutral (tm-hole n)
  n-app    : ∀ {f a} → Neutral f → Neutral (tm-app f a)
  n-case   : ∀ {s m brs} → Neutral s → Neutral (tm-case s m brs)

------------------------------------------------------------------------
-- `Value` = `Canonical` ⊎ `Neutral`, recovering the kernel's notion.
------------------------------------------------------------------------

data Value : Term → Set where
  canonical : ∀ {t} → Canonical t → Value t
  neutral   : ∀ {t} → Neutral t → Value t

-- A closed term is never a neutral: a neutral's head is a free variable,
-- an opaque global, or a hole, none of which is closed-and-final. This is
-- the fact that lets Progress treat the `Neutral` branch as a value.
--
-- OPEN OBLIGATION: proved by induction on `Neutral`, using that a closed
-- term has no free `tm-var` (from `Closed`) and that `tm-global`/`tm-hole`
-- are excluded by `Final` + the signature's totality.
postulate
  closed-not-neutral :
    ∀ {t} → Neutral t → ⊥

