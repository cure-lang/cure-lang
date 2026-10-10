------------------------------------------------------------------------
-- Substitution infrastructure.
--
-- The β and ζ cases of Preservation (docs/SOUNDNESS.md §4) need a
-- substitution lemma: if `Γ , x : A ⊢ b : B` and `Γ ⊢ a : A`, then
-- `Γ ⊢ b[x := a] : B[x := a]`. That lemma in turn needs the algebraic
-- properties of `shift` and `substT` established here.
--
-- This module proves the *syntactic* laws (shift/subst interaction). The
-- typing-level substitution lemma is stated in Proof/Preservation.agda,
-- because it depends on the typing judgment.
--
-- STATUS: the shift/subst laws are the current work; the ones proved so
-- far are marked. The remaining goals are stated with their strategies.
------------------------------------------------------------------------
module Proof.Substitution where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≡ᵇ_; _<_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Core.Syntax

-- Three-argument congruence (not in the stdlib under this name).
cong₃ : ∀ {A B C D : Set} {a a′ : A} {b b′ : B} {c c′ : C}
     → (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- `n + 0 ≡ n`
------------------------------------------------------------------------

+-zero : ∀ n → n + 0 ≡ n
+-zero = +-identityʳ

------------------------------------------------------------------------
-- Shifting by 0 is the identity, at any cutoff.
--
-- This is the base case for the subst laws: `shift 0 c t ≡ t`.
------------------------------------------------------------------------

mutual
  shiftTerms-0 : ∀ c (ts : List Term) → shiftTerms 0 c ts ≡ ts
  shiftTerms-0 c [] = refl
  shiftTerms-0 c (x ∷ xs) = cong₂ _∷_ (shift-0 c x) (shiftTerms-0 c xs)

  shiftBranches-0 : ∀ c (bs : List Branch) → shiftBranches 0 c bs ≡ bs
  shiftBranches-0 c [] = refl
  shiftBranches-0 c (x ∷ xs) = cong₂ _∷_ (shiftBranch-0 c x) (shiftBranches-0 c xs)

  shiftBranch-0 : ∀ c (b : Branch) → shiftBranch 0 c b ≡ b
  shiftBranch-0 c (cn , ar , b) = cong (λ x → cn , ar , x) (shift-0 (c + ar) b)

  shift-0 : ∀ c (t : Term) → shift 0 c t ≡ t
  shift-0 c (tm-type l) = refl
  shift-0 c (tm-var k) with c ≤ᵇ k
  ... | true  = cong tm-var (+-zero k)
  ... | false = refl
  shift-0 c (tm-pi g d b) = cong₂ (tm-pi g) (shift-0 c d) (shift-0 (suc c) b)
  shift-0 c (tm-lam g d b) = cong₂ (tm-lam g) (shift-0 c d) (shift-0 (suc c) b)
  shift-0 c (tm-let g ty v b) = cong₃ (tm-let g) (shift-0 c ty) (shift-0 c v) (shift-0 (suc c) b)
  shift-0 c (tm-app f a) = cong₂ tm-app (shift-0 c f) (shift-0 c a)
  shift-0 c (tm-data n ps is) = cong₂ (tm-data n) (shiftTerms-0 c ps) (shiftTerms-0 c is)
  shift-0 c (tm-ctor n args) = cong (tm-ctor n) (shiftTerms-0 c args)
  shift-0 c (tm-case s m brs) = cong₃ tm-case (shift-0 c s) (shift-0 c m) (shiftBranches-0 c brs)
  shift-0 c (tm-global n) = refl
  shift-0 c (tm-int_type) = refl
  shift-0 c (tm-int_lit k) = refl
  shift-0 c (tm-nat_lit k) = refl
  shift-0 c (tm-bounded_lit k) = refl
  shift-0 c (tm-float_type) = refl
  shift-0 c (tm-float_lit) = refl
  shift-0 c (tm-binary_type) = refl
  shift-0 c (tm-atom_type) = refl
  shift-0 c (tm-atom_lit n) = refl
  shift-0 c (tm-effect_type t) = cong tm-effect_type (shift-0 c t)
  shift-0 c (tm-effect_pure t) = cong tm-effect_pure (shift-0 c t)
  shift-0 c (tm-effect_bind e k) = cong₂ tm-effect_bind (shift-0 c e) (shift-0 c k)
  shift-0 c (tm-hole n) = refl
  shift-0 c (tm-absurd) = refl

------------------------------------------------------------------------
-- Shift on a variable.
--
-- `shift 1 0 (tm-var k) ≡ tm-var (suc k)`: shifting by one a bare variable
-- bumps its index by one. This is the `⇒-var` case of weakening.
------------------------------------------------------------------------

0≤ᵇ : ∀ k → (0 ≤ᵇ k) ≡ true
0≤ᵇ zero = refl
0≤ᵇ (suc k) = 0≤ᵇ k

shift-var-1 : ∀ k → shift 1 0 (tm-var k) ≡ tm-var (suc k)
shift-var-1 k rewrite 0≤ᵇ k = cong tm-var (trans (+-suc k 0) (cong suc (+-identityʳ k)))

------------------------------------------------------------------------
-- Shifting composes.
--
-- `shift a c (shift b c t) ≡ shift (a + b) c t` — two shifts at the same
-- cutoff compose into one. This is needed when weakening a term that is
-- already shifted (the `⇒-app` case, where the codomain is instantiated).
--
-- STATUS: the statement is given; the proof is by induction on the term,
-- with the cutoff bumped under binders. It is the current obligation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Renaming laws.
--
-- `rename` (Core.Syntax) applies an index map to a term. We prove:
--
--   * `ext^ n id ≡ id` — iterating the identity extension is the identity;
--   * `rename-cong`    — pointwise-equal renamings give equal results;
--   * `rename-id`      — renaming by the identity is the identity.
--
-- These are the syntactic backbone of the context-morphism lemma.
------------------------------------------------------------------------

-- `ext^ n id` is the identity, pointwise.
ext-id : ∀ n k → ext^ n (λ j → j) k ≡ k
ext-id zero k = refl
ext-id (suc n) zero = refl
ext-id (suc n) (suc k) = cong suc (ext-id n k)

-- `ext^ n` preserves pointwise equality of renamings.
ext^-cong : ∀ n {ρ σ} → (∀ k → ρ k ≡ σ k) → ∀ k → ext^ n ρ k ≡ ext^ n σ k
ext^-cong zero eq k = eq k
ext^-cong (suc n) eq zero = refl
ext^-cong (suc n) eq (suc k) = cong suc (ext^-cong n eq k)

-- Pointwise-equal renamings give equal results.
mutual
  renameTerms-cong : ∀ {ρ σ} → (∀ k → ρ k ≡ σ k) → ∀ ts → renameTerms ρ ts ≡ renameTerms σ ts
  renameTerms-cong eq [] = refl
  renameTerms-cong eq (x ∷ xs) = cong₂ _∷_ (rename-cong eq x) (renameTerms-cong eq xs)

  renameBranches-cong : ∀ {ρ σ} → (∀ k → ρ k ≡ σ k) → ∀ bs → renameBranches ρ bs ≡ renameBranches σ bs
  renameBranches-cong eq [] = refl
  renameBranches-cong eq (x ∷ xs) = cong₂ _∷_ (renameBranch-cong eq x) (renameBranches-cong eq xs)

  renameBranch-cong : ∀ {ρ σ} → (∀ k → ρ k ≡ σ k) → ∀ b → renameBranch ρ b ≡ renameBranch σ b
  renameBranch-cong {ρ} {σ} eq (cn , ar , b) =
    cong (λ x → cn , ar , x) (rename-cong (ext^-cong ar eq) b)

  rename-cong : ∀ {ρ σ} → (∀ k → ρ k ≡ σ k) → ∀ t → rename ρ t ≡ rename σ t
  rename-cong {ρ} {σ} eq (tm-type l) = refl
  rename-cong {ρ} {σ} eq (tm-var k) = cong tm-var (eq k)
  rename-cong {ρ} {σ} eq (tm-pi g d c) =
    cong₂ (tm-pi g) (rename-cong eq d) (rename-cong (ext^-cong 1 eq) c)
  rename-cong {ρ} {σ} eq (tm-lam g d b) =
    cong₂ (tm-lam g) (rename-cong eq d) (rename-cong (ext^-cong 1 eq) b)
  rename-cong {ρ} {σ} eq (tm-let g ty v b) =
    cong₃ (tm-let g) (rename-cong eq ty) (rename-cong eq v) (rename-cong (ext^-cong 1 eq) b)
  rename-cong {ρ} {σ} eq (tm-app f a) = cong₂ tm-app (rename-cong eq f) (rename-cong eq a)
  rename-cong {ρ} {σ} eq (tm-data n ps is) =
    cong₂ (tm-data n) (renameTerms-cong eq ps) (renameTerms-cong eq is)
  rename-cong {ρ} {σ} eq (tm-ctor n args) = cong (tm-ctor n) (renameTerms-cong eq args)
  rename-cong {ρ} {σ} eq (tm-case s m brs) =
    cong₃ tm-case (rename-cong eq s) (rename-cong eq m) (renameBranches-cong eq brs)
  rename-cong {ρ} {σ} eq (tm-global n) = refl
  rename-cong {ρ} {σ} eq (tm-int_type) = refl
  rename-cong {ρ} {σ} eq (tm-int_lit k) = refl
  rename-cong {ρ} {σ} eq (tm-nat_lit k) = refl
  rename-cong {ρ} {σ} eq (tm-bounded_lit k) = refl
  rename-cong {ρ} {σ} eq (tm-float_type) = refl
  rename-cong {ρ} {σ} eq (tm-float_lit) = refl
  rename-cong {ρ} {σ} eq (tm-binary_type) = refl
  rename-cong {ρ} {σ} eq (tm-atom_type) = refl
  rename-cong {ρ} {σ} eq (tm-atom_lit n) = refl
  rename-cong {ρ} {σ} eq (tm-effect_type t) = cong tm-effect_type (rename-cong eq t)
  rename-cong {ρ} {σ} eq (tm-effect_pure t) = cong tm-effect_pure (rename-cong eq t)
  rename-cong {ρ} {σ} eq (tm-effect_bind e k) = cong₂ tm-effect_bind (rename-cong eq e) (rename-cong eq k)
  rename-cong {ρ} {σ} eq (tm-hole n) = refl
  rename-cong {ρ} {σ} eq (tm-absurd) = refl

-- Renaming by the identity is the identity.
mutual
  renameTerms-id : ∀ ts → renameTerms (λ k → k) ts ≡ ts
  renameTerms-id [] = refl
  renameTerms-id (x ∷ xs) = cong₂ _∷_ (rename-id x) (renameTerms-id xs)

  renameBranches-id : ∀ bs → renameBranches (λ k → k) bs ≡ bs
  renameBranches-id [] = refl
  renameBranches-id (x ∷ xs) = cong₂ _∷_ (renameBranch-id x) (renameBranches-id xs)

  renameBranch-id : ∀ b → renameBranch (λ k → k) b ≡ b
  renameBranch-id (cn , ar , b) =
    trans (cong (λ x → cn , ar , x) (rename-cong (ext-id ar) b))
          (cong (λ x → cn , ar , x) (rename-id b))

  rename-id : ∀ t → rename (λ k → k) t ≡ t
  rename-id (tm-type l) = refl
  rename-id (tm-var k) = refl
  rename-id (tm-pi g d c) =
    trans (cong₂ (tm-pi g) (rename-id d) (rename-cong (ext-id 1) c)) (cong (tm-pi g _) (rename-id c))
  rename-id (tm-lam g d b) =
    trans (cong₂ (tm-lam g) (rename-id d) (rename-cong (ext-id 1) b)) (cong (tm-lam g _) (rename-id b))
  rename-id (tm-let g ty v b) =
    trans (cong₂ (λ x y → tm-let g x y _) (rename-id ty) (rename-id v))
          (cong (λ x → tm-let g _ _ x) (trans (rename-cong (ext-id 1) b) (rename-id b)))
  rename-id (tm-app f a) = cong₂ tm-app (rename-id f) (rename-id a)
  rename-id (tm-data n ps is) = cong₂ (tm-data n) (renameTerms-id ps) (renameTerms-id is)
  rename-id (tm-ctor n args) = cong (tm-ctor n) (renameTerms-id args)
  rename-id (tm-case s m brs) =
    trans (cong₂ (λ x y → tm-case x y _) (rename-id s) (rename-id m))
          (cong (λ x → tm-case _ _ x) (renameBranches-id brs))
  rename-id (tm-global n) = refl
  rename-id (tm-int_type) = refl
  rename-id (tm-int_lit k) = refl
  rename-id (tm-nat_lit k) = refl
  rename-id (tm-bounded_lit k) = refl
  rename-id (tm-float_type) = refl
  rename-id (tm-float_lit) = refl
  rename-id (tm-binary_type) = refl
  rename-id (tm-atom_type) = refl
  rename-id (tm-atom_lit n) = refl
  rename-id (tm-effect_type t) = cong tm-effect_type (rename-id t)
  rename-id (tm-effect_pure t) = cong tm-effect_pure (rename-id t)
  rename-id (tm-effect_bind e k) = cong₂ tm-effect_bind (rename-id e) (rename-id k)
  rename-id (tm-hole n) = refl
  rename-id (tm-absurd) = refl

------------------------------------------------------------------------
-- Substitution is the identity on a term with no free occurrence of the
-- target index.
--
-- `substT j r t ≡ t` when `Scoped j t` (every free variable of `t` is `< j`,
-- so none is `j`). This is the workhorse for the `⇒-var` cases of the
-- substitution lemma: the context's types are `j`-free, so substituting
-- the `j`-th variable leaves them unchanged.
------------------------------------------------------------------------

-- `n ≡ᵇ n` is `true`.
≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- `substT j r (tm-var j) ≡ r`.
subst-var-eq : ∀ {j r} → substT j r (tm-var j) ≡ r
subst-var-eq {j} {r} rewrite ≡ᵇ-refl j = refl

-- `substT j r (tm-var k) ≡ tm-var k` when `k ≢ j`.
subst-var-neq : ∀ {j k r} → (k ≡ᵇ j) ≡ false → substT j r (tm-var k) ≡ tm-var k
subst-var-neq {j} {k} {r} p rewrite p = refl

-- `k < j` gives `(k ≡ᵇ j) ≡ false`.
open import Data.Nat.Properties using (<⇒≢; ≡ᵇ⇒≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T?)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)

<-false : ∀ k j → k < j → (k ≡ᵇ j) ≡ false
<-false k j lt with T? (k ≡ᵇ j)
... | yes t = ⊥-elim (<⇒≢ lt (≡ᵇ⇒≡ k j t))
... | no ¬t with k ≡ᵇ j
...   | false = refl
...   | true  = ⊥-elim (¬t tt)

-- Substitution is the identity on a `j`-scoped term.
mutual
  substTerms-id : ∀ {j r ts} → ScopedTerms j ts → substTerms j r ts ≡ ts
  substTerms-id st[] = refl
  substTerms-id (st∷ sx sxs) = cong₂ _∷_ (subst-id sx) (substTerms-id sxs)

  substBranches-id : ∀ {j r bs} → ScopedBranches j bs → substBranches j r bs ≡ bs
  substBranches-id sb[] = refl
  substBranches-id {j} {r} (sb∷ sx sxs) = cong₂ _∷_ (substBranch-id {j} {r} sx) (substBranches-id {j} {r} sxs)

  substBranch-id : ∀ {j r b} → ScopedBranch j b → substBranch j r b ≡ b
  substBranch-id {j} {r} (sbranch {cn = cn} {ar = ar} {b = b} sb) =
    cong (λ x → cn , ar , x) (subst-id {j = j + ar} {r = shift ar 0 r} sb)

  subst-id : ∀ {j r t} → Scoped j t → substT j r t ≡ t
  subst-id (sc-type {l}) = refl
  subst-id (sc-var {k} k<j) = subst-var-neq {j = _} {k} {r = _} (<-false k _ k<j)
  subst-id (sc-pi sd sc) = cong₂ (tm-pi _) (subst-id sd) (subst-id sc)
  subst-id (sc-lam sd sb) = cong₂ (tm-lam _) (subst-id sd) (subst-id sb)
  subst-id (sc-let st sv sb) = cong₃ (tm-let _) (subst-id st) (subst-id sv) (subst-id sb)
  subst-id (sc-app sf sa) = cong₂ tm-app (subst-id sf) (subst-id sa)
  subst-id (sc-data sps sis) = cong₂ (tm-data _) (substTerms-id sps) (substTerms-id sis)
  subst-id (sc-ctor sargs) = cong (tm-ctor _) (substTerms-id sargs)
  subst-id (sc-case ss sm sbs) = cong₃ tm-case (subst-id ss) (subst-id sm) (substBranches-id sbs)
  subst-id (sc-global {n}) = refl
  subst-id (sc-int_type) = refl
  subst-id (sc-int_lit {k}) = refl
  subst-id (sc-nat_lit {k}) = refl
  subst-id (sc-bounded_lit {k}) = refl
  subst-id (sc-float_type) = refl
  subst-id (sc-float_lit) = refl
  subst-id (sc-binary_type) = refl
  subst-id (sc-atom_type) = refl
  subst-id (sc-atom_lit {n}) = refl
  subst-id (sc-effect_type st) = cong tm-effect_type (subst-id st)
  subst-id (sc-effect_pure st) = cong tm-effect_pure (subst-id st)
  subst-id (sc-effect_bind se sk) = cong₂ tm-effect_bind (subst-id se) (subst-id sk)
  subst-id (sc-hole {n}) = refl
  subst-id (sc-absurd) = refl
