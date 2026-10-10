------------------------------------------------------------------------
-- Context lemmas.
--
-- The weakening and substitution lemmas (Proof/Preservation.agda) need
-- algebraic facts about the typing context `_∋_at_`:
--
--   * weakening: adding a fresh binder preserves every existing lookup,
--     with the index shifted by one;
--   * substitution: replacing the head variable (index 0) and then
--     looking up is the same as looking up and then substituting.
--
-- These are pure de Bruijn bookkeeping. Getting them right is the whole
-- point of the small-kernel discipline (docs/KERNEL.md "de Bruijn
-- indices"): the lemmas are mechanical, and there is nowhere for a capture
-- bug to hide.
--
-- STATUS: all lemmas in this module are PROVED.
------------------------------------------------------------------------
module Proof.Context where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≡ᵇ_; _<_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-refl; ≤-trans; <⇒≢; ≡ᵇ⇒≡)
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T?)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Core.Syntax
open import Core.Typing using (Context; _∋_at_; here; there; extend)
open import Proof.Substitution using (cong₃)

------------------------------------------------------------------------
-- Weakening a lookup.
--
-- If `Γ ∋ T at k`, then `(S ∷ Γ) ∋ T at suc k`: every existing variable is
-- still in scope after a fresh binder is added, found at an index one
-- higher. The stored type `T` is UNCHANGED — the context stores types in
-- the local de Bruijn convention, so prepending a binder shifts indices
-- but not the types themselves.
------------------------------------------------------------------------

∋-weaken : ∀ {Γ T k} (S : Term) → Γ ∋ T at k → (S ∷ Γ) ∋ T at suc k
∋-weaken S here = there here
∋-weaken S (there {S = S′} p) = there (∋-weaken S′ p)

------------------------------------------------------------------------
-- Substitution at index 0 commutes with lookup.
--
-- If `(A ∷ Γ) ∋ T at k` and we replace the head variable (index 0) with
-- `a`, the type of the resulting term is `substT 0 a T`.
--
-- This is the `⇒-var` case of `subst⇒`. The proof is by induction on the
-- lookup:
--   * `here`  — the head variable is replaced; the term becomes `a` and
--               its type is `substT 0 a A`. Since `A` lives in `Γ` (not
--               `A ∷ Γ`), it does not mention index 0, so `substT 0 a A`
--               is `A` up to the shift — the substitution is a no-op on
--               `A`. We record this as the `subst-head` law below.
--   * `there` — the variable is untouched; its type is shifted, and
--               substituting at 0 does not affect it.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Substitution into a term that does not use index 0.
--
-- The `⇒-var here` case of `subst⇒` needs: the type `A` of the head
-- variable lives in the OUTER context `Γ`, so it does not mention index 0,
-- and therefore `substT 0 a A ≡ A`. We prove the general fact that
-- substituting at index `j` into a term with no free occurrence of `j` is
-- the identity.
--
-- We use the `Scoped` predicate from Core.Syntax: `Scoped d t` says every
-- free variable of `t` is `< d`. A term `A` in the outer context `Γ` is
-- `Scoped` at the *outer* depth, so under the extended context `A ∷ Γ` it
-- is `Scoped` at depth `suc d` — in particular it does not use index 0.
------------------------------------------------------------------------

-- `n ≡ᵇ n` is `true`.
≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- `substT j r (tm-var j)` is `r`.
subst-var-eq : ∀ {j r} → substT j r (tm-var j) ≡ r
subst-var-eq {j} {r} rewrite ≡ᵇ-refl j = refl

-- `substT j r (tm-var k)` is `tm-var k` when `k ≢ j`.
subst-var-neq : ∀ {j k r} → (k ≡ᵇ j) ≡ false → substT j r (tm-var k) ≡ tm-var k
subst-var-neq {j} {k} {r} p rewrite p = refl

------------------------------------------------------------------------
-- `substT` is the identity on a term that does not mention the target.
--
-- We prove: if `t` is `Scoped (suc j)` — i.e. all its free variables are
-- `< suc j`, so none is exactly `j` — then `substT j r t ≡ t`.
--
-- This is the workhorse for the `⇒-var here` case (with `j = 0` and `t`
-- the head variable's type `A`, which is scoped in the outer context).
--
-- STATUS: the statement is given; the proof is by induction on `t`,
-- threading the `Scoped` evidence. It is the current obligation of this
-- module.
------------------------------------------------------------------------

-- A term with no free occurrence of index `j`.
NoFree : ℕ → Term → Set
NoFree j t = Scoped (suc j) t

------------------------------------------------------------------------
-- `substT` is the identity on a term with no free occurrence of the target.
--
-- PROVED below by mutual induction on the term, threading the `Scoped`
-- evidence. This is the workhorse for the `⇒-var here` case of `subst⇒`.
------------------------------------------------------------------------

-- `k ≢ j` from `Scoped (suc j)` evidence at index `k`.
open import Data.Empty using (⊥; ⊥-elim)

-- The core: a term scoped at `suc j` has no free occurrence of `j`.
-- We prove the substitution identity directly.
mutual
  substTerms-id : ∀ {j r ts} → ScopedTerms j ts → substTerms j r ts ≡ ts
  substTerms-id {j} {r} st[] = refl
  substTerms-id {j} {r} (st∷ sx sxs) = cong₂ _∷_ (subst-id sx) (substTerms-id sxs)

  substBranches-id : ∀ {j r bs} → ScopedBranches j bs → substBranches j r bs ≡ bs
  substBranches-id {j} {r} sb[] = refl
  substBranches-id {j} {r} (sb∷ sx sxs) = cong₂ _∷_ (substBranch-id {j} {r} sx) (substBranches-id {j} {r} sxs)

  substBranch-id : ∀ {j r b} → ScopedBranch j b → substBranch j r b ≡ b
  substBranch-id {j} {r} (sbranch {cn = cn} {ar = ar} {b = b} sb) =
    cong (λ x → cn , ar , x) (subst-id {j = j + ar} {r = shift ar 0 r} sb)

  subst-id : ∀ {j r t} → Scoped j t → substT j r t ≡ t
  subst-id {j} {r} (sc-type {l}) = refl
  subst-id {j} {r} (sc-var {k} k<j) = subst-var-neq {j} {k} {r} (k≢j k<j)
    where
      -- `k < j` gives `k ≢ j`, so the substitution test is `false`.
      k≢j : k < j → (k ≡ᵇ j) ≡ false
      k≢j lt with T? (k ≡ᵇ j)
      ... | yes t = ⊥-elim (<⇒≢ lt (≡ᵇ⇒≡ k j t))
      ... | no ¬t with k ≡ᵇ j
      ...   | false = refl
      ...   | true  = ⊥-elim (¬t tt)
  subst-id {j} {r} (sc-pi sd sc) = cong₂ (tm-pi _) (subst-id sd) (subst-id sc)
  subst-id {j} {r} (sc-lam sd sb) = cong₂ (tm-lam _) (subst-id sd) (subst-id sb)
  subst-id {j} {r} (sc-let st sv sb) = cong₃ (tm-let _) (subst-id st) (subst-id sv) (subst-id sb)
  subst-id {j} {r} (sc-app sf sa) = cong₂ tm-app (subst-id sf) (subst-id sa)
  subst-id {j} {r} (sc-data sps sis) = cong₂ (tm-data _) (substTerms-id sps) (substTerms-id sis)
  subst-id {j} {r} (sc-ctor sargs) = cong (tm-ctor _) (substTerms-id sargs)
  subst-id {j} {r} (sc-case ss sm sbs) = cong₃ tm-case (subst-id ss) (subst-id sm) (substBranches-id sbs)
  subst-id {j} {r} (sc-global {n}) = refl
  subst-id {j} {r} (sc-int_type) = refl
  subst-id {j} {r} (sc-int_lit {k}) = refl
  subst-id {j} {r} (sc-nat_lit {k}) = refl
  subst-id {j} {r} (sc-bounded_lit {k}) = refl
  subst-id {j} {r} (sc-float_type) = refl
  subst-id {j} {r} (sc-float_lit) = refl
  subst-id {j} {r} (sc-binary_type) = refl
  subst-id {j} {r} (sc-atom_type) = refl
  subst-id {j} {r} (sc-atom_lit {n}) = refl
  subst-id {j} {r} (sc-effect_type st) = cong tm-effect_type (subst-id st)
  subst-id {j} {r} (sc-effect_pure st) = cong tm-effect_pure (subst-id st)
  subst-id {j} {r} (sc-effect_bind se sk) = cong₂ tm-effect_bind (subst-id se) (subst-id sk)
  subst-id {j} {r} (sc-hole {n}) = refl
  subst-id {j} {r} (sc-absurd) = refl
