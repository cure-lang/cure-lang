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
-- A closed term has no free variable: `Scoped 0 (tm-var k)` is absurd.
--
-- A FINDING: the earlier statement `Neutral t → ⊥` ("a closed term is never
-- a neutral") is FALSE. `tm-global n` is closed (`sc-global`) and final
-- (`f-global`) yet neutral (`n-global`) — an opaque global is a legitimate
-- closed value. The only closed neutral heads that are genuinely absurd are
-- the free variable (`tm-var`, ruled out by closedness) and the hole
-- (`tm-hole`, ruled out by `Final`).
--
-- The fact Progress actually consumes is the free-variable one: a closed
-- term cannot be a bare variable. (In the typing judgment the `⇒-var` case
-- is already vacuous, because it needs `Fin 0`, which is empty; this lemma
-- records the underlying syntactic fact for reuse.)
closed-no-var : ∀ {k} → Scoped 0 (tm-var k) → ⊥
closed-no-var (sc-var ())
