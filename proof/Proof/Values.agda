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

-- `Canonical`, `Neutral`, and `Value` are defined in Core.Syntax (the
-- reduction relation needs `Value` for its β/ζ rules); re-exported here.

open import Core.Syntax public using (Canonical; Neutral; Value;
                                      canonical; neutral)

------------------------------------------------------------------------
-- The Canonical/Neutral split is a genuine partition
--
-- `Canonical` and `Neutral` are disjoint by construction: every
-- `Canonical` constructor names an introduction form (`tm-type`, `tm-pi`,
-- `tm-lam`, `tm-data`, `tm-ctor`, the base types/literals, and the effect
-- formers) and every `Neutral` constructor names a stuck computation
-- (`tm-var`, `tm-global`, `tm-hole`, `tm-app`, `tm-case`). No term is both.
--
-- This is what lets the head-inversion lemmas (Proof/Inversion.agda)
-- discharge the elimination rules (`⇒-var`, `⇒-app`, `⇒-case`, `⇒-global`)
-- from a `Canonical` head: their head is neutral, so `Canonical` is absurd.
------------------------------------------------------------------------

canonical-not-neutral : ∀ {t} → Canonical t → Neutral t → ⊥
canonical-not-neutral () (n-var {k})
canonical-not-neutral () (n-global {n})
canonical-not-neutral () (n-hole {n})
canonical-not-neutral () (n-app {f} {a} nf)
canonical-not-neutral () (n-case {s} {m} {brs} ns)
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

