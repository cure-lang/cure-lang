------------------------------------------------------------------------
-- M5a: the δ-unfolding policy and its native simulation.
--
-- `Cure.Core.Normalise` owns the policy between `Eval` and `Quote`:
-- which globals may δ-unfold, under what mode, and with what budget.
-- The native reduction relation (`Core.Reduction`) has exactly ONE δ
-- rule, gated on `Signature.body sig f ≡ just body′` — the visible body.
--
-- The executable policy is strictly richer than that rule. It has
--
--   * three modes — `:certified`, `:reducible`, `:none` — where `:none`
--     refuses every unfold and `:reducible` additionally requires the
--     definition to be marked reducible;
--   * an ALLOWLIST (`delta_allow`) restricting which names may unfold;
--   * a FUEL counter bounding the number of unfolds;
--   * a "lazy unfolding" rule that keeps an application FOLDED when
--     unfolding would only re-expose a stuck eliminator;
--   * an identical-neutral shortcut reporting `:stuck` rather than
--     looping when a certified identity unfolds to itself.
--
-- This module formalises the policy and proves the direction that
-- matters for soundness: EVERY successful policy unfold is a native δ
-- step. The policy's extra conditions only ever REFUSE — they narrow the
-- native rule, never widen it — so no policy success can produce a
-- reduction the native relation does not admit.
--
-- SCOPE. This is the δ policy's SOUNDNESS direction only. It does not
-- prove completeness (that every native δ step is reachable under some
-- policy), does not model the fuel counter's arithmetic (see the M4b
-- finding for why the worker's fuel is a separate obligation), and does
-- not cover stuck-case exposure or the builtin-op fold, which are
-- separate policies with their own typing obligations. No new axiom,
-- hole or checking override is introduced.
------------------------------------------------------------------------
module Core.DeltaPolicy where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Core.Syntax using (Name; Term; tm-global)
open import Core.Reduction using (Signature; _⇝_)
open _⇝_ using (δ)

nothing≠just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≠just ()

------------------------------------------------------------------------
-- The policy, as data.
--
-- Mirrors `Cure.Core.Normalise`'s `delta_mode` and `delta_allow`. The
-- mode is the coarse switch; the allowlist is the per-name refinement;
-- `reducible` is the per-definition flag `:reducible` mode consults.
------------------------------------------------------------------------

data DeltaMode : Set where
  mode-certified mode-reducible mode-none : DeltaMode

-- What the policy needs to know about one global. `visible` is the
-- native `Signature.body` lookup: `nothing` means the body is hidden or
-- absent, which the native δ rule already refuses.
record GlobalInfo : Set where
  constructor global-info
  field
    visible : Maybe Term
    reducible : Bool
open GlobalInfo public

-- The policy's per-name table. A `nothing` entry means the name is not
-- registered at all.
Policy : Set
Policy = Name → Maybe GlobalInfo

-- The allowlist: `nothing` means "no restriction", `just names` means
-- "only these". Mirrors `delta_allow: nil | MapSet.t(atom())`.
Allow : Set
Allow = Maybe (List Name)

member : Name → List Name → Bool
member name [] = false
member name (x ∷ xs) with name ≟ x
... | yes refl = true
... | no _ = member name xs

allowed : Allow → Name → Bool
allowed nothing name = true
allowed (just names) name = member name names

-- The table's visible body for a name.
visible-of : Policy → Name → Maybe Term
visible-of policy name with policy name
... | nothing = nothing
... | just info = visible info

-- `visible-of` at a resolved table entry is that entry's visible field.
visible-of-found : ∀ (policy : Policy) (name : Name) {info : GlobalInfo}
  → policy name ≡ just info
  → visible-of policy name ≡ visible info
visible-of-found policy name found rewrite found = refl


------------------------------------------------------------------------
-- The policy decision.
--
-- `policy-unfold` is the executable's decision procedure, transcribed.
-- It consults, in the executable's order:
--
--   1. the mode: `:none` refuses unconditionally;
--   2. the allowlist;
--   3. the mode-specific condition (`:reducible` needs the flag);
--   4. the visible body.
--
-- Returning `just body` means the policy WILL unfold to `body`.
--
-- Every success branch returns `visible-of policy name` (or, for
-- `:reducible`, the `visible` field at a resolved table entry), so the
-- policy's result and the table's visible body are the same term by
-- construction. That is what makes the simulation theorem go through
-- without equation transport.
------------------------------------------------------------------------

policy-unfold : DeltaMode → Allow → Policy → Name → Maybe Term
policy-unfold mode-none _ _ _ = nothing
policy-unfold mode-certified allow policy name
  with allowed allow name
... | false = nothing
... | true = visible-of policy name
policy-unfold mode-reducible allow policy name
  with allowed allow name
... | false = nothing
... | true with policy name
... | nothing = nothing
... | just info with reducible info
... | false = nothing
... | true = visible info

------------------------------------------------------------------------
-- The simulation theorem.
--
-- Every successful policy unfold is a native δ step. This is the
-- soundness direction: the policy can only ever REFUSE a native step,
-- never invent one.
--
-- The bridge between the policy's `GlobalInfo` table and the native
-- `Signature` is an explicit hypothesis: `body-agrees` says the
-- signature's body lookup agrees with the policy's visible field. That
-- is the representation obligation M2 owns; stating it here keeps the
-- theorem honest about what it assumes.
------------------------------------------------------------------------

record Agrees (policy : Policy) (sig : Signature) : Set where
  field
    body-agrees : ∀ name term → visible-of policy name ≡ just term
      → Signature.body sig name ≡ just term

open Agrees public

-- `:reducible`'s success branch returns the `visible` field at a
-- resolved entry, which is the same term `visible-of` gives.
reducible-visible :
    ∀ (policy : Policy) (name : Name) {info : GlobalInfo} {body : Term}
  → policy name ≡ just info
  → reducible info ≡ true
  → visible info ≡ just body
  → visible-of policy name ≡ just body
reducible-visible policy name {info} {body} found red vis
  rewrite found = vis

-- The theorem: a successful policy unfold is a native δ step.
policy-sound :
    ∀ (mode : DeltaMode) {allow policy sig name body}
  → Agrees policy sig
  → policy-unfold mode allow policy name ≡ just body
  → _⇝_ sig (tm-global name) body
policy-sound mode-certified {allow} {policy} {sig} {name} {body} agrees unfolds
  with allowed allow name
... | false = ⊥-elim (nothing≠just unfolds)
... | true = δ (body-agrees agrees name body unfolds)
policy-sound mode-reducible {allow} {policy} {sig} {name} {body} agrees unfolds
  with allowed allow name
... | false = ⊥-elim (nothing≠just unfolds)
... | true with policy name in found
... | nothing = ⊥-elim (nothing≠just unfolds)
... | just info with reducible info in red
... | false = ⊥-elim (nothing≠just unfolds)
... | true =
  δ (body-agrees agrees name body
       (reducible-visible policy name found red unfolds))
policy-sound mode-none agrees unfolds = ⊥-elim (nothing≠just unfolds)

------------------------------------------------------------------------
-- Negative controls: the policy's refusals.
--
-- These are what make `policy-sound` meaningful. If the policy never
-- refused anything the theorem would be trivial; these record that each
-- guard genuinely narrows the native rule.
------------------------------------------------------------------------

-- `:none` refuses every name, even one with a visible body.
none-refuses :
    ∀ (allow : Allow) (policy : Policy) (name : Name)
  → policy-unfold mode-none allow policy name ≡ nothing
none-refuses allow policy name = refl

-- An empty allowlist refuses every name under `:certified`.
empty-allow-refuses :
    ∀ (policy : Policy) (name : Name)
  → policy-unfold mode-certified (just []) policy name ≡ nothing
empty-allow-refuses policy name = refl

-- An unregistered name is refused under `:certified`.
unregistered-refuses :
    ∀ (allow : Allow) (policy : Policy) (name : Name)
  → policy name ≡ nothing
  → policy-unfold mode-certified allow policy name ≡ nothing
unregistered-refuses allow policy name found
  with allowed allow name
... | false = refl
... | true rewrite found = refl

-- A hidden body is refused under `:certified`.
hidden-refuses :
    ∀ (allow : Allow) (policy : Policy) (name : Name) (info : GlobalInfo)
  → policy name ≡ just info
  → visible info ≡ nothing
  → policy-unfold mode-certified allow policy name ≡ nothing
hidden-refuses allow policy name info found vis
  with allowed allow name
... | false = refl
... | true rewrite visible-of-found policy name found | vis = refl

-- A non-reducible definition is refused under `:reducible`, even with a
-- visible body. This is the mode-specific guard.
not-reducible-refuses :
    ∀ (allow : Allow) (policy : Policy) (name : Name) (info : GlobalInfo)
  → policy name ≡ just info
  → reducible info ≡ false
  → policy-unfold mode-reducible allow policy name ≡ nothing
not-reducible-refuses allow policy name info found red
  with allowed allow name
... | false = refl
... | true rewrite found | red = refl

------------------------------------------------------------------------
-- Positive controls: the policy does unfold when its guards allow.
------------------------------------------------------------------------

-- Under `:certified` with an unrestricted allowlist and a visible body,
-- the policy unfolds.
certified-unfolds :
    ∀ (policy : Policy) (name : Name) {body : Term}
  → visible-of policy name ≡ just body
  → policy-unfold mode-certified nothing policy name ≡ just body
certified-unfolds policy name vis = vis

-- Under `:reducible` with the flag set, the policy unfolds.
reducible-unfolds :
    ∀ (policy : Policy) (name : Name) (info : GlobalInfo) {body : Term}
  → policy name ≡ just info
  → reducible info ≡ true
  → visible info ≡ just body
  → policy-unfold mode-reducible nothing policy name ≡ just body
reducible-unfolds policy name info found red vis
  rewrite found | red = vis
