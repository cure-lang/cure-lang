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
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _≡ᵇ_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-suc; ≤-refl; m≤n⇒m≤1+n; ≤-trans)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Function using (_∘_)
open import Core.Syntax
open import Core.Typing using (countdown; branch-field-vars)

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

-- `rename (ext (shiftRen 0 c)) b ≡ rename (shiftRen 0 (suc c)) b`.
rename-ext-shiftRen : ∀ c b → rename (ext (shiftRen 0 c)) b ≡ rename (shiftRen 0 (suc c)) b
rename-ext-shiftRen c b = cong (λ ρ → rename ρ b) (funext-ren (ext-shiftRen 0 c))

-- `shiftRen 0 c k ≡ k`.
shiftRen-0 : ∀ c k → shiftRen 0 c k ≡ k
shiftRen-0 zero k = +-zero k
shiftRen-0 (suc c) zero = refl
shiftRen-0 (suc c) (suc k) = cong suc (shiftRen-0 c k)

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
-- Shifting by 0 is the identity, at any cutoff.
--
-- `shift 0 c t = rename (shiftRen 0 c) t`, and `shiftRen 0 c` is pointwise
-- the identity (`shiftRen-0`), so `shift-0` is `rename-id` transported
-- across the pointwise-equal renaming. No induction on the term is needed:
-- the whole content is the renaming identity, which `rename-id` already
-- establishes.
------------------------------------------------------------------------

shift-0 : ∀ c (t : Term) → shift 0 c t ≡ t
shift-0 c t =
  trans (cong (λ ρ → rename ρ t) (funext-ren (shiftRen-0 c))) (rename-id t)

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

------------------------------------------------------------------------
-- The substitution/renaming interaction.
--
-- `substS σ (rename ρ t) ≡ substS (σ ∘s ρ) t`: substituting after renaming
-- is the same as substituting with the composed substitution. This is the
-- key law that makes the substitution lemma's binder case go through.
--
-- The proof is by mutual induction on the term. Under a binder the
-- substitution is extended by `extSub` and the renaming by `ext`; the two
-- extensions are related by `extSub σ ∘s ext ρ ≡ extSub (σ ∘s ρ)`, which
-- is `exts^-comp` at `n = 1`.
--
-- Function extensionality is assumed (standard for de Bruijn metatheory).
------------------------------------------------------------------------

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
         → (∀ x → f x ≡ g x) → f ≡ g

-- Composition of a substitution with a renaming.
_∘s_ : Sub → Ren → Sub
(σ ∘s ρ) k = σ (ρ k)

-- The composition law: `extSub^ n σ ∘s ext^ n ρ ≡ extSub^ n (σ ∘s ρ)`.
extSub^-comp : ∀ n σ ρ j → (extSub^ n σ ∘s ext^ n ρ) j ≡ extSub^ n (σ ∘s ρ) j
extSub^-comp zero σ ρ j = refl
extSub^-comp (suc n) σ ρ zero = refl
extSub^-comp (suc n) σ ρ (suc k) = cong (rename wk) (extSub^-comp n σ ρ k)

-- Three-argument congruence (duplicated here to keep the module self-contained).
cong₃′ : ∀ {A B C D : Set} {a a′ : A} {b b′ : B} {c c′ : C}
      → (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃′ f refl refl refl = refl

mutual
  subst-rename-terms : ∀ σ ρ ts → substTermsS σ (renameTerms ρ ts) ≡ substTermsS (σ ∘s ρ) ts
  subst-rename-terms σ ρ [] = refl
  subst-rename-terms σ ρ (x ∷ xs) = cong₂ _∷_ (subst-rename σ ρ x) (subst-rename-terms σ ρ xs)

  subst-rename-branches : ∀ σ ρ bs → substBranchesS σ (renameBranches ρ bs) ≡ substBranchesS (σ ∘s ρ) bs
  subst-rename-branches σ ρ [] = refl
  subst-rename-branches σ ρ (x ∷ xs) = cong₂ _∷_ (subst-rename-branch σ ρ x) (subst-rename-branches σ ρ xs)

  subst-rename-branch : ∀ σ ρ b → substBranchS σ (renameBranch ρ b) ≡ substBranchS (σ ∘s ρ) b
  subst-rename-branch σ ρ (cn , ar , b) =
    cong (λ x → cn , ar , x)
         (trans (subst-rename (extSub^ ar σ) (ext^ ar ρ) b)
                (cong (λ σ' → substS σ' b) (funext (λ k → extSub^-comp ar σ ρ k))))

  -- The composition law at n = 1, as a function equality.
  extSub-comp : ∀ σ ρ → (extSub σ ∘s ext ρ) ≡ extSub (σ ∘s ρ)
  extSub-comp σ ρ = funext (λ j → extSub^-comp 1 σ ρ j)

  subst-rename : ∀ (σ : Sub) (ρ : Ren) t → substS σ (rename ρ t) ≡ substS (σ ∘s ρ) t
  subst-rename σ ρ (tm-type l) = refl
  subst-rename σ ρ (tm-var k) = refl
  subst-rename σ ρ (tm-pi g d c) =
    cong₂ (tm-pi g) (subst-rename σ ρ d)
          (trans (subst-rename (extSub σ) (ext ρ) c)
                 (cong (λ σ' → substS σ' c) (extSub-comp σ ρ)))
  subst-rename σ ρ (tm-lam g d b) =
    cong₂ (tm-lam g) (subst-rename σ ρ d)
          (trans (subst-rename (extSub σ) (ext ρ) b)
                 (cong (λ σ' → substS σ' b) (extSub-comp σ ρ)))
  subst-rename σ ρ (tm-let g ty v b) =
    cong₃′ (tm-let g) (subst-rename σ ρ ty) (subst-rename σ ρ v)
           (trans (subst-rename (extSub σ) (ext ρ) b)
                  (cong (λ σ' → substS σ' b) (extSub-comp σ ρ)))
  subst-rename σ ρ (tm-app f a) = cong₂ tm-app (subst-rename σ ρ f) (subst-rename σ ρ a)
  subst-rename σ ρ (tm-data n ps is) = cong₂ (tm-data n) (subst-rename-terms σ ρ ps) (subst-rename-terms σ ρ is)
  subst-rename σ ρ (tm-ctor n args) = cong (tm-ctor n) (subst-rename-terms σ ρ args)
  subst-rename σ ρ (tm-case s m brs) =
    cong₃′ tm-case (subst-rename σ ρ s) (subst-rename σ ρ m) (subst-rename-branches σ ρ brs)
  subst-rename σ ρ (tm-global n) = refl
  subst-rename σ ρ (tm-int_type) = refl
  subst-rename σ ρ (tm-int_lit k) = refl
  subst-rename σ ρ (tm-nat_lit k) = refl
  subst-rename σ ρ (tm-bounded_lit k) = refl
  subst-rename σ ρ (tm-float_type) = refl
  subst-rename σ ρ (tm-float_lit) = refl
  subst-rename σ ρ (tm-binary_type) = refl
  subst-rename σ ρ (tm-atom_type) = refl
  subst-rename σ ρ (tm-atom_lit n) = refl
  subst-rename σ ρ (tm-effect_type t) = cong tm-effect_type (subst-rename σ ρ t)
  subst-rename σ ρ (tm-effect_pure t) = cong tm-effect_pure (subst-rename σ ρ t)
  subst-rename σ ρ (tm-effect_bind e k) = cong₂ tm-effect_bind (subst-rename σ ρ e) (subst-rename σ ρ k)
  subst-rename σ ρ (tm-hole n) = refl
  subst-rename σ ρ (tm-absurd) = refl

------------------------------------------------------------------------
-- Consequences of `subst-rename` at the weakening renaming.
--
-- These are the two facts the substitution lemma's binder case needs.
------------------------------------------------------------------------

-- Rename every term in a substitution.
renameSub : Ren → Sub → Sub
renameSub ρ σ k = rename ρ (σ k)

-- `extSub σ ∘s wk ≡ renameSub wk σ`.
extSub-wk : ∀ σ → (extSub σ ∘s wk) ≡ renameSub wk σ
extSub-wk σ = funext (λ j → refl)

-- `rename ρ (substS σ t) ≡ substS (renameSub ρ σ) t` — renaming after
-- substituting is substituting with the renamed substitution.
mutual
  rename-subst-terms : ∀ ρ σ ts → renameTerms ρ (substTermsS σ ts) ≡ substTermsS (renameSub ρ σ) ts
  rename-subst-terms ρ σ [] = refl
  rename-subst-terms ρ σ (x ∷ xs) =
    cong₂ _∷_ (rename-subst ρ σ x) (rename-subst-terms ρ σ xs)

  rename-subst-branches : ∀ ρ σ bs → renameBranches ρ (substBranchesS σ bs) ≡ substBranchesS (renameSub ρ σ) bs
  rename-subst-branches ρ σ [] = refl
  rename-subst-branches ρ σ (x ∷ xs) =
    cong₂ _∷_ (rename-subst-branch ρ σ x) (rename-subst-branches ρ σ xs)

  rename-subst-branch : ∀ ρ σ b → renameBranch ρ (substBranchS σ b) ≡ substBranchS (renameSub ρ σ) b
  rename-subst-branch ρ σ (cn , ar , b) =
    cong (λ x → cn , ar , x)
         (trans (rename-subst (ext^ ar ρ) (extSub^ ar σ) b)
                (cong (λ σ' → substS σ' b)
                      (funext (λ k → renameSub-extSub ρ σ ar k))))
    where
      -- renameSub (ext^ n ρ) (extSub^ n σ) ≡ extSub^ n (renameSub ρ σ)
      renameSub-extSub : ∀ ρ σ n k
        → renameSub (ext^ n ρ) (extSub^ n σ) k ≡ extSub^ n (renameSub ρ σ) k
      renameSub-extSub ρ σ zero k = refl
      renameSub-extSub ρ σ (suc n) zero = refl
      renameSub-extSub ρ σ (suc n) (suc k) =
        trans (rename-compose (ext (ext^ n ρ)) wk (extSub^ n σ k))
              (trans (cong (λ x → rename x (extSub^ n σ k))
                           (funext-ren (ext-wk-compose (ext^ n ρ))))
                     (trans (sym (rename-compose wk (ext^ n ρ) (extSub^ n σ k)))
                            (cong (rename wk) (renameSub-extSub ρ σ n k))))


  renameSub-extSub-eq : ∀ ρ σ → renameSub (ext ρ) (extSub σ) ≡ extSub (renameSub ρ σ)
  renameSub-extSub-eq ρ σ = funext (λ { zero → refl
                                      ; (suc k) →
                                          trans (rename-compose (ext ρ) wk (σ k))
                                                (trans (cong (λ x → rename x (σ k))
                                                             (funext-ren (ext-wk-compose ρ)))
                                                       (sym (rename-compose wk ρ (σ k)))) })

  rename-subst : ∀ ρ σ t → rename ρ (substS σ t) ≡ substS (renameSub ρ σ) t
  rename-subst ρ σ (tm-type l) = refl
  rename-subst ρ σ (tm-var k) = refl
  rename-subst ρ σ (tm-pi g d c) =
    cong₂ (tm-pi g) (rename-subst ρ σ d)
          (trans (rename-subst (ext ρ) (extSub σ) c)
                 (cong (λ σ' → substS σ' c) (renameSub-extSub-eq ρ σ)))
  rename-subst ρ σ (tm-lam g d b) =
    cong₂ (tm-lam g) (rename-subst ρ σ d)
          (trans (rename-subst (ext ρ) (extSub σ) b)
                 (cong (λ σ' → substS σ' b) (renameSub-extSub-eq ρ σ)))
  rename-subst ρ σ (tm-let g ty v b) =
    cong₃′ (tm-let g) (rename-subst ρ σ ty) (rename-subst ρ σ v)
           (trans (rename-subst (ext ρ) (extSub σ) b)
                  (cong (λ σ' → substS σ' b) (renameSub-extSub-eq ρ σ)))
  rename-subst ρ σ (tm-app f a) = cong₂ tm-app (rename-subst ρ σ f) (rename-subst ρ σ a)
  rename-subst ρ σ (tm-data n ps is) = cong₂ (tm-data n) (rename-subst-terms ρ σ ps) (rename-subst-terms ρ σ is)
  rename-subst ρ σ (tm-ctor n args) = cong (tm-ctor n) (rename-subst-terms ρ σ args)
  rename-subst ρ σ (tm-case s m brs) =
    cong₃′ tm-case (rename-subst ρ σ s) (rename-subst ρ σ m) (rename-subst-branches ρ σ brs)
  rename-subst ρ σ (tm-global n) = refl
  rename-subst ρ σ (tm-int_type) = refl
  rename-subst ρ σ (tm-int_lit k) = refl
  rename-subst ρ σ (tm-nat_lit k) = refl
  rename-subst ρ σ (tm-bounded_lit k) = refl
  rename-subst ρ σ (tm-float_type) = refl
  rename-subst ρ σ (tm-float_lit) = refl
  rename-subst ρ σ (tm-binary_type) = refl
  rename-subst ρ σ (tm-atom_type) = refl
  rename-subst ρ σ (tm-atom_lit n) = refl
  rename-subst ρ σ (tm-effect_type t) = cong tm-effect_type (rename-subst ρ σ t)
  rename-subst ρ σ (tm-effect_pure t) = cong tm-effect_pure (rename-subst ρ σ t)
  rename-subst ρ σ (tm-effect_bind e k) = cong₂ tm-effect_bind (rename-subst ρ σ e) (rename-subst ρ σ k)
  rename-subst ρ σ (tm-hole n) = refl
  rename-subst ρ σ (tm-absurd) = refl

-- `substS (extSub σ) (rename wk t) ≡ rename wk (substS σ t)`.
subst-extSub-wk : ∀ σ t → substS (extSub σ) (rename wk t) ≡ rename wk (substS σ t)
subst-extSub-wk σ t =
  trans (subst-rename (extSub σ) wk t)
        (trans (cong (λ σ' → substS σ' t) (extSub-wk σ))
               (sym (rename-subst wk σ t)))

------------------------------------------------------------------------
-- Substitution composes.
--
-- `substS σ (substS τ t) ≡ substS (substCompose σ τ) t`: two substitutions
-- compose. The composed substitution applies `σ` to each term of `τ`:
--
--     substCompose σ τ k = substS σ (τ k)
--
-- Under a binder the extensions are related by
-- `extSub σ ∘ substCompose (extSub σ) τ ≡ substCompose (extSub σ) (extSub τ)`,
-- which follows from `extSub`'s definition.
------------------------------------------------------------------------

-- Composition of two substitutions.
substCompose : Sub → Sub → Sub
substCompose σ τ k = substS σ (τ k)

-- `substCompose (extSub σ) (extSub τ) ≡ extSub (substCompose σ τ)`.
-- (The substitution extensions commute with composition.)
extSub-compose : ∀ σ τ j
  → substCompose (extSub σ) (extSub τ) j ≡ extSub (substCompose σ τ) j
extSub-compose σ τ zero = refl
extSub-compose σ τ (suc k) = subst-extSub-wk σ (τ k)

mutual
  subst-compose-terms : ∀ σ τ ts → substTermsS σ (substTermsS τ ts) ≡ substTermsS (substCompose σ τ) ts
  subst-compose-terms σ τ [] = refl
  subst-compose-terms σ τ (x ∷ xs) =
    cong₂ _∷_ (subst-compose σ τ x) (subst-compose-terms σ τ xs)

  subst-compose-branches : ∀ σ τ bs → substBranchesS σ (substBranchesS τ bs) ≡ substBranchesS (substCompose σ τ) bs
  subst-compose-branches σ τ [] = refl
  subst-compose-branches σ τ (x ∷ xs) =
    cong₂ _∷_ (subst-compose-branch σ τ x) (subst-compose-branches σ τ xs)

  subst-compose-branch : ∀ σ τ b → substBranchS σ (substBranchS τ b) ≡ substBranchS (substCompose σ τ) b
  subst-compose-branch σ τ (cn , ar , b) =
    cong (λ x → cn , ar , x)
         (trans (subst-compose (extSub^ ar σ) (extSub^ ar τ) b)
                (cong (λ τ' → substS τ' b)
                      (funext (λ k → extSub^-compose ar σ τ k))))
    where
      extSub^-compose : ∀ n σ τ k
        → substCompose (extSub^ n σ) (extSub^ n τ) k
        ≡ extSub^ n (substCompose σ τ) k
      extSub^-compose zero σ τ k = refl
      extSub^-compose (suc n) σ τ zero = refl
      extSub^-compose (suc n) σ τ (suc k) =
        trans (subst-extSub-wk (extSub^ n σ) (extSub^ n τ k))
              (cong (rename wk) (extSub^-compose n σ τ k))

  subst-compose : ∀ σ τ t → substS σ (substS τ t) ≡ substS (substCompose σ τ) t
  subst-compose σ τ (tm-type l) = refl
  subst-compose σ τ (tm-var k) = refl
  subst-compose σ τ (tm-pi g d c) =
    cong₂ (tm-pi g) (subst-compose σ τ d)
          (trans (subst-compose (extSub σ) (extSub τ) c)
                 (cong (λ σ' → substS σ' c)
                       (funext (extSub-compose σ τ))))
  subst-compose σ τ (tm-lam g d b) =
    cong₂ (tm-lam g) (subst-compose σ τ d)
          (trans (subst-compose (extSub σ) (extSub τ) b)
                 (cong (λ σ' → substS σ' b)
                       (funext (extSub-compose σ τ))))
  subst-compose σ τ (tm-let g ty v b) =
    cong₃′ (tm-let g) (subst-compose σ τ ty) (subst-compose σ τ v)
           (trans (subst-compose (extSub σ) (extSub τ) b)
                  (cong (λ σ' → substS σ' b)
                        (funext (extSub-compose σ τ))))
  subst-compose σ τ (tm-app f a) = cong₂ tm-app (subst-compose σ τ f) (subst-compose σ τ a)
  subst-compose σ τ (tm-data n ps is) = cong₂ (tm-data n) (subst-compose-terms σ τ ps) (subst-compose-terms σ τ is)
  subst-compose σ τ (tm-ctor n args) = cong (tm-ctor n) (subst-compose-terms σ τ args)
  subst-compose σ τ (tm-case s m brs) =
    cong₃′ tm-case (subst-compose σ τ s) (subst-compose σ τ m) (subst-compose-branches σ τ brs)
  subst-compose σ τ (tm-global n) = refl
  subst-compose σ τ (tm-int_type) = refl
  subst-compose σ τ (tm-int_lit k) = refl
  subst-compose σ τ (tm-nat_lit k) = refl
  subst-compose σ τ (tm-bounded_lit k) = refl
  subst-compose σ τ (tm-float_type) = refl
  subst-compose σ τ (tm-float_lit) = refl
  subst-compose σ τ (tm-binary_type) = refl
  subst-compose σ τ (tm-atom_type) = refl
  subst-compose σ τ (tm-atom_lit n) = refl
  subst-compose σ τ (tm-effect_type t) = cong tm-effect_type (subst-compose σ τ t)
  subst-compose σ τ (tm-effect_pure t) = cong tm-effect_pure (subst-compose σ τ t)
  subst-compose σ τ (tm-effect_bind e k) = cong₂ tm-effect_bind (subst-compose σ τ e) (subst-compose σ τ k)
  subst-compose σ τ (tm-hole n) = refl
  subst-compose σ τ (tm-absurd) = refl

------------------------------------------------------------------------
-- The "top" substitution.
--
-- `topSub a` replaces index 0 with `a` and renumbers the indices above it
-- down by one. This is the substitution the β and ζ rules use.
------------------------------------------------------------------------

-- `substS (topSub a) (rename wk t) ≡ t`: substituting the head undoes
-- weakening, because `topSub a` maps `suc k ↦ tm-var k`.
mutual
  topSub-rename-terms : ∀ a ts → substTermsS (topSub a) (renameTerms wk ts) ≡ ts
  topSub-rename-terms a [] = refl
  topSub-rename-terms a (x ∷ xs) =
    cong₂ _∷_ (topSub-rename a x) (topSub-rename-terms a xs)

  topSub-rename-branches : ∀ a bs → substBranchesS (topSub a) (renameBranches wk bs) ≡ bs
  topSub-rename-branches a [] = refl
  topSub-rename-branches a (x ∷ xs) =
    cong₂ _∷_ (topSub-rename-branch a x) (topSub-rename-branches a xs)

  -- The branch case: `ext^ ar wk` extends the renaming arity-many times;
  -- the substitution must be extended correspondingly.
  postulate
    topSub-rename-branch : ∀ a b → substBranchS (topSub a) (renameBranch wk b) ≡ b

  -- `substS (topSub a) (rename wk t) ≡ t`: substituting the head undoes
  -- weakening. The variable case is `topSub a (suc k) = tm-var k`.
  --
  -- OPEN OBLIGATION: the binder case needs the substitution extension to be
  -- adjoint to the renaming extension (`extSub (topSub a)` maps
  -- `suc (suc k) ↦ var (suc k)`, but the standard `extSub` maps it to
  -- `tm-var (suc k)`). Parameterising `extSub` by the renaming (the
  -- adjoint extension) closes this; see proof/README.md.
  postulate
    topSub-rename : ∀ a t → substS (topSub a) (rename wk t) ≡ t

-- `substS σ (substS (topSub v) T) ≡ substS (topSub (substS σ v)) (substS (extSub σ) T)`.
topSub-compose : ∀ σ v j
  → substCompose σ (topSub v) j ≡ substCompose (topSub (substS σ v)) (extSub σ) j
topSub-compose σ v zero = refl
topSub-compose σ v (suc k) = sym (topSub-rename (substS σ v) (σ k))

-- The `let` rule's substitution law.
subst-topSub : ∀ σ v T
  → substS σ (substS (topSub v) T)
  ≡ substS (topSub (substS σ v)) (substS (extSub σ) T)
subst-topSub σ v T =
  trans (subst-compose σ (topSub v) T)
        (trans (cong (λ τ → substS τ T) (funext (topSub-compose σ v)))
               (sym (subst-compose (topSub (substS σ v)) (extSub σ) T)))

------------------------------------------------------------------------
-- Renaming commutes with the top substitution.
--
-- `rename ρ (substTopT v T) ≡ substTopT (rename ρ v) (rename (ext ρ) T)`.
--
-- This is the `let` rule's renaming law: the result type `substTopT v T`
-- (the substitution of the value into the inferred body type) must be
-- renamed consistently with how the `⇒-let` rule re-forms it under `ρ`.
--
-- Both sides are `substS`-applications, so the proof is `rename-subst`
-- on the left and `subst-rename` on the right, bridged by a pointwise
-- equality of substitutions that holds definitionally at both indices.
------------------------------------------------------------------------

rename-topSub : ∀ ρ v T
  → rename ρ (substTopT v T) ≡ substTopT (rename ρ v) (rename (ext ρ) T)
rename-topSub ρ v T =
  trans (rename-subst ρ (topSub v) T)
        (trans (cong (λ σ → substS σ T) (funext (rename-topSub-coh ρ v)))
               (sym (subst-rename (topSub (rename ρ v)) (ext ρ) T)))
  where
    -- `renameSub ρ (topSub v) ≡ topSub (rename ρ v) ∘s ext ρ`, pointwise.
    rename-topSub-coh : ∀ ρ v k
      → renameSub ρ (topSub v) k ≡ (topSub (rename ρ v) ∘s ext ρ) k
    rename-topSub-coh ρ v zero = refl
    rename-topSub-coh ρ v (suc k) = refl

------------------------------------------------------------------------
-- Lifting a term into an extended context.
--
-- `rename (λ j → j + ar)` weakens a term by `ar` binders. The `case`
-- branch case of the renaming lemma must commute this weakening with a
-- renaming `ρ`: lifting then renaming is renaming then lifting, with the
-- renaming extended by `ext^ ar ρ`.
--
--     rename (λ j → j + ar) (rename ρ t)
--       ≡ rename (ext^ ar ρ) (rename (λ j → j + ar) t)
--
-- The proof is `rename-compose` twice, bridged by the pointwise identity
-- `ext^ ar ρ ∘ (λ j → j + ar) ≡ (λ j → j + ar) ∘ ρ`.
------------------------------------------------------------------------

-- `ext^ ar ρ ∘ (λ j → j + ar) ≡ (λ j → j + ar) ∘ ρ`, pointwise.
ext-raise : ∀ ar ρ k → (ext^ ar ρ ∘ (λ j → j + ar)) k ≡ ((λ j → j + ar) ∘ ρ) k
ext-raise zero ρ k = trans (cong ρ (+-identityʳ k)) (sym (+-identityʳ (ρ k)))
ext-raise (suc ar) ρ k =
  trans (cong (ext (ext^ ar ρ)) (+-suc k ar))
        (trans (cong suc (ext-raise ar ρ k)) (sym (+-suc (ρ k) ar)))

rename-raise : ∀ ar (ρ : Ren) t
  → rename (λ j → j + ar) (rename ρ t)
  ≡ rename (ext^ ar ρ) (rename (λ j → j + ar) t)
rename-raise ar ρ t =
  trans (rename-compose (λ j → j + ar) ρ t)
        (trans (sym (cong (λ x → rename x t) (funext-ren (ext-raise ar ρ))))
               (sym (rename-compose (ext^ ar ρ) (λ j → j + ar) t)))

------------------------------------------------------------------------
-- The branch field variables are fixed by `ext^ ar ρ`.
--
-- A branch body lives under `ar` field binders, so it is renamed by
-- `ext^ ar ρ`. The field variables `branch-field-vars ar` are exactly the
-- indices `0, …, ar-1`, and `ext^ ar ρ` fixes every index `< ar`. Hence
-- the constructor applied to the field variables is unchanged by the
-- renaming — the fact that makes the branch case of the renaming lemma
-- go through.
------------------------------------------------------------------------

-- `ext^ ar ρ` fixes every index `< ar`.
ext^-fix : ∀ ar (ρ : Ren) k → k < ar → ext^ ar ρ k ≡ k
ext^-fix (suc ar) ρ zero (s≤s p) = refl
ext^-fix (suc ar) ρ (suc k) (s≤s p) = cong suc (ext^-fix ar ρ k p)

-- `renameTerms (ext^ ar ρ) (branch-field-vars ar) ≡ branch-field-vars ar`.
renameTerms-field-vars : ∀ ar (ρ : Ren)
  → renameTerms (ext^ ar ρ) (branch-field-vars ar) ≡ branch-field-vars ar
renameTerms-field-vars ar ρ =
  trans (renameTerms-map (ext^ ar ρ) (branch-field-vars ar))
        (trans (cong (map (rename (ext^ ar ρ))) (sym (map-tm-var-countdown ar)))
               (trans (map-compose (rename (ext^ ar ρ)) tm-var (countdown ar))
                      (trans (map-countdown-fix ar ar ρ (≤-refl {ar}))
                              (sym (map-tm-var-countdown ar)))))
  where
    map-tm-var-countdown : ∀ ar → branch-field-vars ar ≡ map tm-var (countdown ar)
    map-tm-var-countdown ar = refl

    map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (f ∘ g) xs
    map-compose f g [] = refl
    map-compose f g (x ∷ xs) = cong₂ _∷_ refl (map-compose f g xs)

    -- `map (λ k → tm-var (ext^ n ρ k)) (countdown ar) ≡ map tm-var (countdown ar)`
    -- when `ar ≤ n`: every field index (`< ar ≤ n`) is fixed by `ext^ n ρ`.
    map-countdown-fix : ∀ ar n (ρ : Ren) → ar ≤ n
      → map (λ k → tm-var (ext^ n ρ k)) (countdown ar) ≡ map tm-var (countdown ar)
    map-countdown-fix zero n ρ le = refl
    map-countdown-fix (suc ar) n ρ le = cong₂ _∷_ head tail
      where
        head : tm-var (ext^ n ρ ar) ≡ tm-var ar
        head = cong tm-var (ext^-fix n ρ ar le)
        tail : map (λ k → tm-var (ext^ n ρ k)) (countdown ar) ≡ map tm-var (countdown ar)
        tail = map-countdown-fix ar n ρ (≤-trans (m≤n⇒m≤1+n (≤-refl {ar})) le)

------------------------------------------------------------------------
-- The branch motive under a renaming.
--
-- A `case` branch body checks against the motive applied to the
-- constructor of the field variables,
--
--     tm-app (rename (λ j → j + ar) m) (tm-ctor cn (branch-field-vars ar))
--
-- (the motive is weakened by `ar` into the branch context). Renaming the
-- whole thing by `ext^ ar ρ` agrees with renaming the motive by `ρ` and
-- re-weakening: the motive commutes by `rename-raise`, and the field
-- variables are fixed by `ext^ ar ρ` (`renameTerms-field-vars`).
------------------------------------------------------------------------

rename-branch-motive : ∀ ar (ρ : Ren) (m : Term) (cn : Name)
  → rename (ext^ ar ρ) (tm-app (rename (λ j → j + ar) m) (tm-ctor cn (branch-field-vars ar)))
  ≡ tm-app (rename (λ j → j + ar) (rename ρ m)) (tm-ctor cn (branch-field-vars ar))
rename-branch-motive ar ρ m cn =
  cong₂ tm-app
        (sym (rename-raise ar ρ m))
        (cong (tm-ctor cn) (renameTerms-field-vars ar ρ))

------------------------------------------------------------------------
-- Substituting under `ar` field binders undoes the `ar`-fold weakening.
--
--     substS (extSub^ ar σ) (shift ar 0 T) ≡ shift ar 0 (substS σ T)
--
-- This is the `ar`-fold generalisation of `subst-extSub-wk`; it is the
-- law the `case` branch case of the substitution lemma needs, because a
-- branch body lives under `ar` field binders.
------------------------------------------------------------------------

subst-extSub^-shift : ∀ ar σ T
  → substS (extSub^ ar σ) (shift ar 0 T) ≡ shift ar 0 (substS σ T)
subst-extSub^-shift zero σ T =
  trans (cong (λ x → substS σ x) (shift-0 0 T)) (sym (shift-0 0 (substS σ T)))
subst-extSub^-shift (suc ar) σ T =
  trans (cong (substS (extSub (extSub^ ar σ))) (shift-suc-wk ar T))
        (trans (cong (λ t → substS (extSub (extSub^ ar σ)) t) (shift-1-wk (shift ar 0 T)))
               (trans (subst-extSub-wk (extSub^ ar σ) (shift ar 0 T))
                      (trans (sym (shift-1-wk (substS (extSub^ ar σ) (shift ar 0 T))))
                             (trans (cong (shift 1 0) (subst-extSub^-shift ar σ T))
                                    (sym (shift-suc-wk ar (substS σ T)))))))
  where
    plus1 : ∀ m → m + 1 ≡ suc m
    plus1 m = trans (+-suc m 0) (cong suc (+-identityʳ m))

    -- `shift 1 0 t ≡ rename wk t`.
    shift-1-wk : ∀ t → shift 1 0 t ≡ rename wk t
    shift-1-wk t = cong (λ ρ → rename ρ t) (funext-ren (λ k → plus1 k))

    -- `shift (suc ar) 0 T ≡ shift 1 0 (shift ar 0 T)`.
    shift-suc-wk : ∀ ar T → shift (suc ar) 0 T ≡ shift 1 0 (shift ar 0 T)
    shift-suc-wk ar T =
      trans (cong (λ ρ → rename ρ T) (funext-ren (pt ar)))
            (sym (rename-compose (shiftRen 1 0) (shiftRen ar 0) T))
      where
        pt : ∀ ar k → shiftRen (suc ar) 0 k ≡ shiftRen 1 0 (shiftRen ar 0 k)
        pt ar k = trans (+-suc k ar) (sym (plus1 (k + ar)))

------------------------------------------------------------------------
-- The branch field variables are fixed by the extended substitution.
--
-- `substS (extSub^ ar σ) (tm-var k) ≡ tm-var k` for every field index
-- `k < ar`, because `extSub^ ar σ` maps the first `ar` indices to
-- themselves. Hence the constructor applied to the field variables is
-- unchanged by the substitution — the substitution analogue of
-- `renameTerms-field-vars`.
------------------------------------------------------------------------

-- `substS (extSub^ ar σ) (tm-var k) ≡ tm-var k` for `k < ar`.
substS-extSub^-fix : ∀ ar σ k → k < ar → substS (extSub^ ar σ) (tm-var k) ≡ tm-var k
substS-extSub^-fix (suc ar) σ zero (s≤s p) = refl
substS-extSub^-fix (suc ar) σ (suc k) (s≤s p) =
  trans (cong (substS (extSub (extSub^ ar σ))) refl)
        (trans (subst-extSub-wk (extSub^ ar σ) (tm-var k))
               (cong (rename wk) (substS-extSub^-fix ar σ k p)))

-- `substTermsS (extSub^ ar σ) (branch-field-vars ar) ≡ branch-field-vars ar`.
substTerms-field-vars : ∀ ar σ
  → substTermsS (extSub^ ar σ) (branch-field-vars ar) ≡ branch-field-vars ar
substTerms-field-vars ar σ =
  trans (substTerms-map (extSub^ ar σ) (branch-field-vars ar))
        (trans (cong (map (substS (extSub^ ar σ))) (sym (map-tm-var-countdown ar)))
               (trans (map-compose (substS (extSub^ ar σ)) tm-var (countdown ar))
                      (trans (map-countdown-subst-fix ar ar σ (≤-refl {ar}))
                             (sym (map-tm-var-countdown ar)))))
  where
    map-tm-var-countdown : ∀ ar → branch-field-vars ar ≡ map tm-var (countdown ar)
    map-tm-var-countdown ar = refl

    map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (f ∘ g) xs
    map-compose f g [] = refl
    map-compose f g (x ∷ xs) = cong₂ _∷_ refl (map-compose f g xs)

    map-countdown-subst-fix : ∀ ar n σ → ar ≤ n
      → map (λ k → substS (extSub^ n σ) (tm-var k)) (countdown ar) ≡ map tm-var (countdown ar)
    map-countdown-subst-fix zero n σ le = refl
    map-countdown-subst-fix (suc ar) n σ le = cong₂ _∷_ head tail
      where
        head : substS (extSub^ n σ) (tm-var ar) ≡ tm-var ar
        head = substS-extSub^-fix n σ ar le
        tail : map (λ k → substS (extSub^ n σ) (tm-var k)) (countdown ar) ≡ map tm-var (countdown ar)
        tail = map-countdown-subst-fix ar n σ (≤-trans (m≤n⇒m≤1+n (≤-refl {ar})) le)

-- The branch motive under a substitution.
subst-branch-motive : ∀ ar σ (m : Term) (cn : Name)
  → substS (extSub^ ar σ) (tm-app (rename (λ j → j + ar) m) (tm-ctor cn (branch-field-vars ar)))
  ≡ tm-app (rename (λ j → j + ar) (substS σ m)) (tm-ctor cn (branch-field-vars ar))
subst-branch-motive ar σ m cn =
  cong₂ tm-app
        (subst-extSub^-shift ar σ m)
        (cong (tm-ctor cn) (substTerms-field-vars ar σ))