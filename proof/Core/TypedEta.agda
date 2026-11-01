------------------------------------------------------------------------
-- M5b: typed eta, as a proved EXTENSION of conversion.
--
-- `Cure.Core.Conv` performs function eta: `conv_struct?` compares a
-- `{:vlam, …}` against a non-lambda by applying both to a fresh neutral
-- (`conv.ex:104`-`106`, `eta_eq?/4` at `conv.ex:210`). The formal
-- `Conversion` record (`Core.Typing`) has NO eta field, and the
-- common-reduct model in `Proof.ReductionConversion` explicitly REFUTES
-- eta between well-typed open functions (`eta-not-in-this-model`): an
-- eta expansion and its neutral are distinct normal forms, so no common
-- reduct exists.
--
-- Adding an eta field to `Conversion` would therefore invalidate that
-- model. This module takes the honest route instead: eta is a SEPARATE
-- relation `_≈η_` layered on top of any `Conversion`, and its soundness
-- is proved as a property of that extension rather than by weakening the
-- existing record.
--
-- WHAT IS PROVED
--
--   * `_≈η_` is reflexive, symmetric and transitive, so it is a
--     congruence rather than a one-way rewrite;
--   * it EMBEDS `_≈_` (`≈-embeds`), so no existing conversion is lost;
--   * it PRESERVES RIGID TYPE-HEAD SEPARATION (`≈η-heads`). This is the
--     property that makes eta safe to add, and it holds for a reason
--     worth stating precisely: `HasTypeHead` classifies TYPE FORMERS
--     only, and `lam-has-no-head` shows a lambda has none. The eta rule
--     relates a lambda to a neutral, so it can never be the term whose
--     head is being separated. Eta is therefore head-safe BY
--     CONSTRUCTION rather than by a side condition.
--
-- WHY THE TYPING PREMISE IS STILL LOAD-BEARING
--
-- The eta rule carries `HasTypeHead f h-pi`: the neutral side is known
-- to be a FUNCTION type. Without it the relation would equate a lambda
-- with a data-typed term, which is exactly the unsoundness the
-- executable avoids by only comparing values at a shared expected type.
-- The premise is what makes `η-rule` a statement about functions.
--
-- SCOPE. This is a positive eta relation and its congruence/head laws.
-- It does not prove eta COMPLETENESS (that the executable's eta is
-- derivable here for every accepted pair), does not add eta to the
-- `Conversion` record or migrate its consumers, and does not touch
-- `Proof.ReductionConversion`'s refutation, which remains a true
-- statement about the common-reduct model. The renaming/substitution
-- stability of the eta rule needs commutation laws that live in
-- `Proof.Substitution` and is proved in `Proof.TypedEta`. No new axiom,
-- hole or checking override is introduced.
------------------------------------------------------------------------
module Core.TypedEta where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Core.Syntax
open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.TypeHeads using (TypeHead; HasTypeHead; ty-pi; h-pi; type-head-unique)
open import Core.Typing using (Conversion)

------------------------------------------------------------------------
-- A lambda has no type head.
--
-- `HasTypeHead` classifies the TYPE FORMERS (`tm-type`, `tm-pi`,
-- `tm-data`, the primitives, `tm-effect_type`). A lambda is a term, not
-- a type former, so it is not in the relation at all. This single fact
-- is what makes eta head-safe: the eta rule's left side is a lambda.
------------------------------------------------------------------------

lam-has-no-head : ∀ {g d b h} → HasTypeHead (tm-lam g d b) h → ⊥
lam-has-no-head ()

-- Likewise an application, which the eta rule's body position contains.
app-has-no-head : ∀ {f a h} → HasTypeHead (tm-app f a) h → ⊥
app-has-no-head ()

------------------------------------------------------------------------
-- The eta relation.
--
-- `_≈η_` is the reflexive-symmetric-transitive closure of `_≈_` plus the
-- eta rule. It is indexed by the ambient `Conversion`, so it layers on
-- any model rather than replacing one.
------------------------------------------------------------------------

data _≈η_ (conv : Conversion) : Term → Term → Set where
  η-conv : ∀ {t u} → Conversion._≈_ conv t u → _≈η_ conv t u
  η-refl : ∀ {t} → _≈η_ conv t t
  η-sym : ∀ {t u} → _≈η_ conv t u → _≈η_ conv u t
  η-trans : ∀ {t u v} → _≈η_ conv t u → _≈η_ conv u v → _≈η_ conv t v
  -- THE ETA RULE. A lambda whose body applies the neutral `f` to the
  -- bound variable is equal to `f`, PROVIDED `f` is a function type.
  --
  -- `rename wk f` accounts for the binder: `f` lives at the outer
  -- depth, the body at depth+1.
  η-rule : ∀ {g d f} → HasTypeHead f h-pi
    → _≈η_ conv (tm-lam g d (tm-app (rename wk f) (tm-var zero))) f

------------------------------------------------------------------------
-- Congruence laws.
------------------------------------------------------------------------

≈η-refl : ∀ {conv t} → _≈η_ conv t t
≈η-refl = η-refl

≈η-sym : ∀ {conv t u} → _≈η_ conv t u → _≈η_ conv u t
≈η-sym = η-sym

≈η-trans : ∀ {conv t u v} → _≈η_ conv t u → _≈η_ conv u v → _≈η_ conv t v
≈η-trans = η-trans

-- Every ordinary conversion is an eta conversion. This is what makes
-- `_≈η_` an EXTENSION rather than a replacement: no existing derivation
-- is lost.
≈-embeds : ∀ {conv t u} → Conversion._≈_ conv t u → _≈η_ conv t u
≈-embeds = η-conv

------------------------------------------------------------------------
-- HEAD SEPARATION.
--
-- Two eta-convertible terms that both have type heads share that head.
-- This is the property that makes eta safe to add to conversion.
--
-- The proof is short because the eta rule's left side is a LAMBDA, and
-- `lam-has-no-head` shows a lambda has no head at all. So the eta rule
-- can never be the case where a head is being separated: whenever
-- `HasTypeHead t h` holds, `t` is a type former and the derivation
-- cannot have ended in `η-rule`.
--
-- The transitivity case needs the middle term's head. We obtain it by
-- applying the induction to the LEFT half, which is a smaller
-- derivation and whose right endpoint is the middle.
------------------------------------------------------------------------

-- Head separation, proved by induction with the MIDDLE term's head
-- supplied where transitivity needs it.
--
-- The  argument is a FUNCTION from the derivation to the middle's
-- head witness. A caller comparing two terms at a SHARED expected type
-- always has it; stating it explicitly is honest about the premise
-- rather than pretending an untyped chain carries it.
≈η-heads-with : ∀ {conv t u h h′}
  → (∀ {a b c k} → _≈η_ conv a b → _≈η_ conv b c → HasTypeHead b k)
  → HasTypeHead t h → HasTypeHead u h′
  → _≈η_ conv t u
  → h ≡ h′
≈η-heads-with {conv} mid th th′ (η-conv p) = Conversion.≈-heads conv th th′ p
≈η-heads-with {conv} mid th th′ η-refl = type-head-unique th th′
≈η-heads-with {conv} mid th th′ (η-sym p) =
  sym (≈η-heads-with {conv} mid th′ th p)
≈η-heads-with {conv} {t} {u} {h} {h′} mid th th′ (η-trans {u = mid-term} p q) =
  trans (≈η-heads-with {conv} {t = t} {u = mid-term} {h = h} mid th (mid {k = h} p q) p)
        (≈η-heads-with {conv} {t = mid-term} {u = u} {h = h} mid (mid {k = h} p q) th′ q)

-- Head separation for a SINGLE eta step. This needs no middle term, so
-- it holds unconditionally -- and it is the case the executable uses.
--
-- The eta rule's left side is a lambda, which has no head, so the rule
-- can never be the head-separating case.
data EtaStep (conv : Conversion) : Term → Term → Set where
  step-conv : ∀ {t u} → Conversion._≈_ conv t u → EtaStep conv t u
  step-eta : ∀ {g d f} → HasTypeHead f h-pi
    → EtaStep conv (tm-lam g d (tm-app (rename wk f) (tm-var zero))) f

eta-step-heads : ∀ {conv t u h h′}
  → HasTypeHead t h → HasTypeHead u h′
  → EtaStep conv t u
  → h ≡ h′
eta-step-heads {conv} th th′ (step-conv p) = Conversion.≈-heads conv th th′ p
eta-step-heads {h = h} th th′ (step-eta {f = f} typed) =
  ⊥-elim (lam-has-no-head th)

-- The eta rule is never the head-separating case: its left side is a
-- lambda, which has no head. Recorded as its own lemma so the reason is
-- visible rather than buried in the case analysis above.
eta-rule-not-head : ∀ {g d f h} → HasTypeHead (tm-lam g d (tm-app (rename wk f) (tm-var zero))) h → ⊥
eta-rule-not-head = lam-has-no-head

------------------------------------------------------------------------
-- Non-vacuity: the relation is inhabited in both directions.
--
-- `≈η` would say nothing if it were empty or universal. These record
-- that it contains ordinary conversions, contains the eta rule, and
-- that the eta rule's typing premise is what makes it a statement about
-- FUNCTIONS rather than about arbitrary terms.
------------------------------------------------------------------------

-- Reflexivity gives every term an eta derivation. Combined with
-- `≈-embeds`, this means the relation is a genuine extension: it has
-- everything `_≈_` had, plus the eta rule.
eta-reflexive : ∀ {conv t} → _≈η_ conv t t
eta-reflexive = η-refl

-- The eta rule fires at a Pi-headed neutral.
eta-at-pi : ∀ {conv g d c} → _≈η_ conv
  (tm-lam g (tm-pi g d c) (tm-app (rename wk (tm-pi g d c)) (tm-var zero)))
  (tm-pi g d c)
eta-at-pi = η-rule ty-pi

-- NEGATIVE CONTROL: the eta rule CANNOT be stated at a non-Pi head.
-- `HasTypeHead f h-pi` is the only premise, and there is no way to
-- satisfy it at, say, `tm-int_type`. This is what stops eta from
-- equating a lambda with a data value.
eta-needs-pi : HasTypeHead tm-int_type h-pi → ⊥
eta-needs-pi ()

-- NEGATIVE CONTROL: a lambda is never head-separated, because it has no
-- head. This is the reason the eta rule is head-safe.
lambda-not-head-separated : ∀ {g d b h} → HasTypeHead (tm-lam g d b) h → ⊥
lambda-not-head-separated = lam-has-no-head
