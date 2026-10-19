------------------------------------------------------------------------
-- Substitution infrastructure.
--
-- The β and ζ cases of Preservation (docs/SOUNDNESS.md §4) need a
-- substitution lemma: if `Γ , x : A ⊢ b : B` and `Γ ⊢ a : A`, then
-- `Γ ⊢ b[x := a] : B[x := a]`. That lemma in turn needs the algebraic
-- properties of `shift` and the simultaneous substitution `substS`
-- established here.
--
-- This module proves the *syntactic* laws (shift/subst interaction). The
-- typing-level substitution lemma is stated in Proof/Preservation.agda,
-- because it depends on the typing judgment.
--
-- STATUS: the shift/subst laws are the current work; the ones proved so
-- far are marked. The remaining goals are stated with their strategies.
------------------------------------------------------------------------
module Proof.Substitution where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-suc; +-comm; ≤-refl; m≤n⇒m≤1+n; ≤-trans)
open import Data.List using (List; []; _∷_; _++_; map; length; reverse)
open import Data.List.Properties using (reverse-map; length-reverse)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Function using (_∘_)
open import Core.Syntax
open import Core.Typing using (upto; branch-field-vars; surface-field-vars)
open import Core.Reduction using (argsSub; argsSub-go; argsSub-go-raise; substArgs)

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
-- Substitution is the identity on a closed term.
--
-- The development uses a SINGLE substitution presentation: the simultaneous
-- substitution `substS : Sub → Term → Term` (Core.Syntax). The legacy
-- targeted substitution `substT` has been removed; the closedness facts it
-- used to provide are the `substS-scoped` / `substS-closed` lemmas below.
------------------------------------------------------------------------

ext^-fix : ∀ ar (ρ : Ren) k → k < ar → ext^ ar ρ k ≡ k
ext^-fix (suc ar) ρ zero (s≤s p) = refl
ext^-fix (suc ar) ρ (suc k) (s≤s p) = cong suc (ext^-fix ar ρ k p)

-- `ext^ ar ρ` on `ar + j` is `ar + ρ j`.
ext^-raise : ∀ ar (ρ : Ren) j → ext^ ar ρ (ar + j) ≡ ar + ρ j
ext^-raise zero ρ j = refl
ext^-raise (suc ar) ρ j = cong suc (ext^-raise ar ρ j)

-- Every index is either below `ar` or of the form `ar + j`.
lt-or : ∀ ar k → k < ar ⊎ (Σ ℕ (λ j → k ≡ ar + j))
lt-or zero k = inj₂ (k , refl)
lt-or (suc ar) zero = inj₁ (s≤s z≤n)
lt-or (suc ar) (suc k) with lt-or ar k
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ (j , refl) = inj₂ (j , refl)

-- Cancel `ar +` on a strict inequality.
lt-cancel : ∀ ar j d → ar + j < ar + d → j < d
lt-cancel zero j d p = p
lt-cancel (suc ar) j d (s≤s p) = lt-cancel ar j d p

-- `ext^ ar ρ` fixes every index `< d + ar` when `ρ` fixes every index `< d`.
ext^-fix+ : ∀ ar (ρ : Ren) d → (∀ k → k < d → ρ k ≡ k)
          → ∀ k → k < d + ar → ext^ ar ρ k ≡ k
ext^-fix+ ar ρ d h k p with lt-or ar k
... | inj₁ q = ext^-fix ar ρ k q
... | inj₂ (j , refl) = trans (ext^-raise ar ρ j) (cong (ar +_) (h j (lt-cancel′ ar j d p)))
  where
    -- `ar + j < d + ar` implies `j < d`.
    lt-cancel′ : ∀ ar j d → ar + j < d + ar → j < d
    lt-cancel′ ar j d p = lt-cancel ar j d (subst (λ Z → ar + j < Z) (+-comm d ar) p)

------------------------------------------------------------------------
-- Renaming a scoped term.
--
-- A term scoped at `d` is fixed by any renaming that fixes every index
-- `< d`. In particular a CLOSED term (`Scoped 0`) is fixed by every
-- renaming — the fact that the signature's telescopes and declared types
-- are closed, so renaming/substitution leaves them unchanged.
------------------------------------------------------------------------

mutual
  rename-scoped : ∀ {d ρ} {t : Term} → Scoped d t
                → (∀ k → k < d → ρ k ≡ k) → rename ρ t ≡ t
  rename-scoped (sc-type {l}) h = refl
  rename-scoped (sc-var {k} k<d) h = cong tm-var (h k k<d)
  rename-scoped (sc-pi sd sc) h = cong₂ (tm-pi _) (rename-scoped sd h) (rename-scoped sc (ext-ok h))
  rename-scoped (sc-lam sd sb) h = cong₂ (tm-lam _) (rename-scoped sd h) (rename-scoped sb (ext-ok h))
  rename-scoped (sc-let st sv sb) h = cong₃ (tm-let _) (rename-scoped st h) (rename-scoped sv h) (rename-scoped sb (ext-ok h))
  rename-scoped (sc-app sf sa) h = cong₂ tm-app (rename-scoped sf h) (rename-scoped sa h)
  rename-scoped (sc-data sps sis) h = cong₂ (tm-data _) (renameTerms-scoped sps h) (renameTerms-scoped sis h)
  rename-scoped (sc-ctor sargs) h = cong (tm-ctor _) (renameTerms-scoped sargs h)
  rename-scoped (sc-case ss sm sbs) h = cong₃ tm-case (rename-scoped ss h) (rename-scoped sm h) (renameBranches-scoped sbs h)
  rename-scoped (sc-global {n}) h = refl
  rename-scoped (sc-int_type) h = refl
  rename-scoped (sc-int_lit {k}) h = refl
  rename-scoped (sc-nat_lit {k}) h = refl
  rename-scoped (sc-bounded_lit {k}) h = refl
  rename-scoped (sc-float_type) h = refl
  rename-scoped (sc-float_lit) h = refl
  rename-scoped (sc-binary_type) h = refl
  rename-scoped (sc-atom_type) h = refl
  rename-scoped (sc-atom_lit {n}) h = refl
  rename-scoped (sc-effect_type st) h = cong tm-effect_type (rename-scoped st h)
  rename-scoped (sc-effect_pure st) h = cong tm-effect_pure (rename-scoped st h)
  rename-scoped (sc-effect_bind se sk) h = cong₂ tm-effect_bind (rename-scoped se h) (rename-scoped sk h)
  rename-scoped (sc-hole {n}) h = refl
  rename-scoped (sc-absurd) h = refl

  ext-ok : ∀ {d ρ} → (∀ k → k < d → ρ k ≡ k) → (∀ k → k < suc d → ext ρ k ≡ k)
  ext-ok h zero p = refl
  ext-ok h (suc k) (s≤s p) = cong suc (h k p)

  renameTerms-scoped : ∀ {d ρ} {ts} → ScopedTerms d ts
                     → (∀ k → k < d → ρ k ≡ k) → renameTerms ρ ts ≡ ts
  renameTerms-scoped st[] h = refl
  renameTerms-scoped (st∷ sx sxs) h = cong₂ _∷_ (rename-scoped sx h) (renameTerms-scoped sxs h)

  renameBranches-scoped : ∀ {d ρ} {bs} → ScopedBranches d bs
                        → (∀ k → k < d → ρ k ≡ k) → renameBranches ρ bs ≡ bs
  renameBranches-scoped sb[] h = refl
  renameBranches-scoped (sb∷ sx sxs) h = cong₂ _∷_ (renameBranch-scoped sx h) (renameBranches-scoped sxs h)

  renameBranch-scoped : ∀ {d ρ} {b} → ScopedBranch d b
                      → (∀ k → k < d → ρ k ≡ k) → renameBranch ρ b ≡ b
  renameBranch-scoped {d = d} {ρ = ρ} (sbranch {cn = cn} {ar = ar} {b = b} sb) h =
    cong (λ x → cn , ar , x) (rename-scoped sb (ext^-fix+ ar ρ d h))

-- A CLOSED term is fixed by every renaming.
rename-closed : ∀ {ρ} {t : Term} → Scoped 0 t → rename ρ t ≡ t
rename-closed st = rename-scoped st (λ k ())

-- `extSub^ ar σ` fixes every index `< ar` (maps it to its own variable).
extSub^-fix : ∀ ar (σ : Sub) k → k < ar → extSub^ ar σ k ≡ tm-var k
extSub^-fix (suc ar) σ zero (s≤s p) = refl
extSub^-fix (suc ar) σ (suc k) (s≤s p) = cong (rename wk) (extSub^-fix ar σ k p)

-- `shiftRen a 0 k ≡ k + a` (the `a`-fold weakening).
shiftRen-k0 : ∀ a k → shiftRen a 0 k ≡ k + a
shiftRen-k0 zero k = refl
shiftRen-k0 (suc a) k = refl

-- `extSub^ ar σ` on `ar + j` is `rename (shiftRen ar 0) (σ j)`.
extSub^-raise : ∀ ar (σ : Sub) j → extSub^ ar σ (ar + j) ≡ rename (shiftRen ar 0) (σ j)
extSub^-raise zero σ j = sym (shift-0 0 (σ j))
extSub^-raise (suc ar) σ j =
  trans (cong (rename wk) (extSub^-raise ar σ j))
        (trans (rename-compose wk (shiftRen ar 0) (σ j))
               (cong (λ ρ → rename ρ (σ j)) (funext-ren (wk-shiftRen ar))))
  where
    wk-shiftRen : ∀ ar k → (wk ∘ shiftRen ar 0) k ≡ shiftRen (suc ar) 0 k
    wk-shiftRen ar k = sym (+-suc k ar)

-- `extSub^ ar σ` fixes every index `< d + ar` when `σ` fixes every index `< d`.
extSub^-fix+ : ∀ ar (σ : Sub) d → (∀ k → k < d → σ k ≡ tm-var k)
             → ∀ k → k < d + ar → extSub^ ar σ k ≡ tm-var k
extSub^-fix+ ar σ d h k p with lt-or ar k
... | inj₁ q = extSub^-fix ar σ k q
... | inj₂ (j , refl) =
  trans (extSub^-raise ar σ j)
        (trans (cong (rename (shiftRen ar 0)) (h j (lt-cancel′ ar j d p)))
               (rename-var-shiftRen ar j))
  where
    lt-cancel′ : ∀ ar j d → ar + j < d + ar → j < d
    lt-cancel′ ar j d p = lt-cancel ar j d (subst (λ Z → ar + j < Z) (+-comm d ar) p)
    rename-var-shiftRen : ∀ ar j → rename (shiftRen ar 0) (tm-var j) ≡ tm-var (ar + j)
    rename-var-shiftRen ar j = cong tm-var (trans (shiftRen-k0 ar j) (+-comm j ar))

-- A term scoped at `d` is fixed by any substitution that fixes every index
-- `< d` (maps it to its own variable).
mutual
  substS-scoped : ∀ {d σ} {t : Term} → Scoped d t
                → (∀ k → k < d → σ k ≡ tm-var k) → substS σ t ≡ t
  substS-scoped (sc-type {l}) h = refl
  substS-scoped (sc-var {k} k<d) h = h k k<d
  substS-scoped (sc-pi sd sc) h = cong₂ (tm-pi _) (substS-scoped sd h) (substS-scoped sc (extSub-ok h))
  substS-scoped (sc-lam sd sb) h = cong₂ (tm-lam _) (substS-scoped sd h) (substS-scoped sb (extSub-ok h))
  substS-scoped (sc-let st sv sb) h = cong₃ (tm-let _) (substS-scoped st h) (substS-scoped sv h) (substS-scoped sb (extSub-ok h))
  substS-scoped (sc-app sf sa) h = cong₂ tm-app (substS-scoped sf h) (substS-scoped sa h)
  substS-scoped (sc-data sps sis) h = cong₂ (tm-data _) (substTermsS-scoped sps h) (substTermsS-scoped sis h)
  substS-scoped (sc-ctor sargs) h = cong (tm-ctor _) (substTermsS-scoped sargs h)
  substS-scoped (sc-case ss sm sbs) h = cong₃ tm-case (substS-scoped ss h) (substS-scoped sm h) (substBranchesS-scoped sbs h)
  substS-scoped (sc-global {n}) h = refl
  substS-scoped (sc-int_type) h = refl
  substS-scoped (sc-int_lit {k}) h = refl
  substS-scoped (sc-nat_lit {k}) h = refl
  substS-scoped (sc-bounded_lit {k}) h = refl
  substS-scoped (sc-float_type) h = refl
  substS-scoped (sc-float_lit) h = refl
  substS-scoped (sc-binary_type) h = refl
  substS-scoped (sc-atom_type) h = refl
  substS-scoped (sc-atom_lit {n}) h = refl
  substS-scoped (sc-effect_type st) h = cong tm-effect_type (substS-scoped st h)
  substS-scoped (sc-effect_pure st) h = cong tm-effect_pure (substS-scoped st h)
  substS-scoped (sc-effect_bind se sk) h = cong₂ tm-effect_bind (substS-scoped se h) (substS-scoped sk h)
  substS-scoped (sc-hole {n}) h = refl
  substS-scoped (sc-absurd) h = refl

  extSub-ok : ∀ {d σ} → (∀ k → k < d → σ k ≡ tm-var k)
            → (∀ k → k < suc d → extSub σ k ≡ tm-var k)
  extSub-ok h zero p = refl
  extSub-ok h (suc k) (s≤s p) = cong (rename wk) (h k p)

  substTermsS-scoped : ∀ {d σ} {ts} → ScopedTerms d ts
                     → (∀ k → k < d → σ k ≡ tm-var k) → substTermsS σ ts ≡ ts
  substTermsS-scoped st[] h = refl
  substTermsS-scoped (st∷ sx sxs) h = cong₂ _∷_ (substS-scoped sx h) (substTermsS-scoped sxs h)

  substBranchesS-scoped : ∀ {d σ} {bs} → ScopedBranches d bs
                        → (∀ k → k < d → σ k ≡ tm-var k) → substBranchesS σ bs ≡ bs
  substBranchesS-scoped sb[] h = refl
  substBranchesS-scoped (sb∷ sx sxs) h = cong₂ _∷_ (substBranchS-scoped sx h) (substBranchesS-scoped sxs h)

  substBranchS-scoped : ∀ {d σ} {b} → ScopedBranch d b
                      → (∀ k → k < d → σ k ≡ tm-var k) → substBranchS σ b ≡ b
  substBranchS-scoped {d = d} {σ = σ} (sbranch {cn = cn} {ar = ar} {b = b} sb) h =
    cong (λ x → cn , ar , x) (substS-scoped sb (extSub^-fix+ ar σ d h))

-- A CLOSED term is fixed by every substitution.
substS-closed : ∀ {σ} {t : Term} → Scoped 0 t → substS σ t ≡ t
substS-closed st = substS-scoped st (λ k ())

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
-- Function extensionality (`funext`, Core.Syntax) is the development's single
-- axiom.
------------------------------------------------------------------------

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

-- `substS (λ k → tm-var k) t ≡ t`: the identity substitution is the
-- identity. (The `substS` analogue of `rename-id`.)
mutual
  substTermsS-idSub : ∀ ts → substTermsS (λ k → tm-var k) ts ≡ ts
  substTermsS-idSub [] = refl
  substTermsS-idSub (x ∷ xs) = cong₂ _∷_ (substS-idSub x) (substTermsS-idSub xs)

  substBranchesS-idSub : ∀ bs → substBranchesS (λ k → tm-var k) bs ≡ bs
  substBranchesS-idSub [] = refl
  substBranchesS-idSub (x ∷ xs) = cong₂ _∷_ (substBranchS-idSub x) (substBranchesS-idSub xs)

  substBranchS-idSub : ∀ b → substBranchS (λ k → tm-var k) b ≡ b
  substBranchS-idSub (cn , ar , b) =
    cong (λ x → cn , ar , x)
         (trans (cong (λ σ → substS σ b)
                      (funext (λ k → extSub^-idSub ar k)))
                (substS-idSub b))
    where
      extSub^-idSub : ∀ ar k → extSub^ ar (λ j → tm-var j) k ≡ tm-var k
      extSub^-idSub zero k = refl
      extSub^-idSub (suc ar) zero = refl
      extSub^-idSub (suc ar) (suc k) = cong (rename wk) (extSub^-idSub ar k)

  -- `extSub` fixes the identity substitution.
  extSub-idSub : ∀ k → extSub (λ j → tm-var j) k ≡ tm-var k
  extSub-idSub zero = refl
  extSub-idSub (suc k) = refl

  substS-idSub : ∀ t → substS (λ k → tm-var k) t ≡ t
  substS-idSub (tm-type l) = refl
  substS-idSub (tm-var k) = refl
  substS-idSub (tm-pi g d c) =
    cong₂ (tm-pi g) (substS-idSub d)
          (trans (cong (λ σ → substS σ c) (funext extSub-idSub)) (substS-idSub c))
  substS-idSub (tm-lam g d b) =
    cong₂ (tm-lam g) (substS-idSub d)
          (trans (cong (λ σ → substS σ b) (funext extSub-idSub)) (substS-idSub b))
  substS-idSub (tm-let g ty v b) =
    cong₃ (tm-let g) (substS-idSub ty) (substS-idSub v)
          (trans (cong (λ σ → substS σ b) (funext extSub-idSub)) (substS-idSub b))
  substS-idSub (tm-app f a) = cong₂ tm-app (substS-idSub f) (substS-idSub a)
  substS-idSub (tm-data n ps is) = cong₂ (tm-data n) (substTermsS-idSub ps) (substTermsS-idSub is)
  substS-idSub (tm-ctor n args) = cong (tm-ctor n) (substTermsS-idSub args)
  substS-idSub (tm-case s m brs) = cong₃ tm-case (substS-idSub s) (substS-idSub m) (substBranchesS-idSub brs)
  substS-idSub (tm-global n) = refl
  substS-idSub (tm-int_type) = refl
  substS-idSub (tm-int_lit k) = refl
  substS-idSub (tm-nat_lit k) = refl
  substS-idSub (tm-bounded_lit k) = refl
  substS-idSub (tm-float_type) = refl
  substS-idSub (tm-float_lit) = refl
  substS-idSub (tm-binary_type) = refl
  substS-idSub (tm-atom_type) = refl
  substS-idSub (tm-atom_lit n) = refl
  substS-idSub (tm-effect_type t) = cong tm-effect_type (substS-idSub t)
  substS-idSub (tm-effect_pure t) = cong tm-effect_pure (substS-idSub t)
  substS-idSub (tm-effect_bind e k) = cong₂ tm-effect_bind (substS-idSub e) (substS-idSub k)
  substS-idSub (tm-hole n) = refl
  substS-idSub (tm-absurd) = refl

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

  -- The key composition: `extSub^ ar (topSub a) ∘ ext^ ar wk` is the
  -- IDENTITY substitution. This is what dissolves the "adjoint extension"
  -- obstruction: the `ar`-fold extended substitution is exactly inverse to
  -- the `ar`-fold extended weakening, so the branch case is `subst-id`.
  extSub^-topSub-ext^-wk : ∀ ar a k
    → (extSub^ ar (topSub a) ∘s ext^ ar wk) k ≡ tm-var k
  extSub^-topSub-ext^-wk zero a k = refl
  extSub^-topSub-ext^-wk (suc ar) a zero = refl
  extSub^-topSub-ext^-wk (suc ar) a (suc k) =
    cong (rename wk) (extSub^-topSub-ext^-wk ar a k)

  -- The branch case: the extended substitution is inverse to the extended
  -- weakening, so the branch body is unchanged.
  topSub-rename-branch : ∀ a b → substBranchS (topSub a) (renameBranch wk b) ≡ b
  topSub-rename-branch a (cn , ar , b) =
    cong (λ x → cn , ar , x)
         (trans (subst-rename (extSub^ ar (topSub a)) (ext^ ar wk) b)
                (trans (cong (λ σ → substS σ b)
                             (funext (λ k → extSub^-topSub-ext^-wk ar a k)))
                       (substS-idSub b)))

  -- `substS (topSub a) (rename wk t) ≡ t`: substituting the head undoes
  -- weakening. The binder case uses the composition identity
  -- `extSub (topSub a) ∘ ext wk ≡ idSub`; the branch case is
  -- `topSub-rename-branch`.
  --
  -- The binder case:
  --   substS (extSub (topSub a)) (rename (ext wk) b)
  --     = substS (extSub (topSub a) ∘s ext wk) b   (subst-rename)
  --     = substS idSub b                            (extSub-topSub-ext-wk)
  --     = b                                          (substS-idSub)
  topSub-rename : ∀ a t → substS (topSub a) (rename wk t) ≡ t
  topSub-rename a (tm-type l) = refl
  topSub-rename a (tm-var k) = refl
  topSub-rename a (tm-pi g d c) =
    cong₂ (tm-pi g) (topSub-rename a d) (topSub-rename-binder a c)
  topSub-rename a (tm-lam g d b) =
    cong₂ (tm-lam g) (topSub-rename a d) (topSub-rename-binder a b)
  topSub-rename a (tm-let g ty v b) =
    cong₃ (tm-let g) (topSub-rename a ty) (topSub-rename a v) (topSub-rename-binder a b)
  topSub-rename a (tm-app f x) = cong₂ tm-app (topSub-rename a f) (topSub-rename a x)
  topSub-rename a (tm-data n ps is) = cong₂ (tm-data n) (topSub-rename-terms a ps) (topSub-rename-terms a is)
  topSub-rename a (tm-ctor n args) = cong (tm-ctor n) (topSub-rename-terms a args)
  topSub-rename a (tm-case s m brs) =
    cong₃ tm-case (topSub-rename a s) (topSub-rename a m) (topSub-rename-branches a brs)
  topSub-rename a (tm-global n) = refl
  topSub-rename a (tm-int_type) = refl
  topSub-rename a (tm-int_lit k) = refl
  topSub-rename a (tm-nat_lit k) = refl
  topSub-rename a (tm-bounded_lit k) = refl
  topSub-rename a (tm-float_type) = refl
  topSub-rename a (tm-float_lit) = refl
  topSub-rename a (tm-binary_type) = refl
  topSub-rename a (tm-atom_type) = refl
  topSub-rename a (tm-atom_lit n) = refl
  topSub-rename a (tm-effect_type t) = cong tm-effect_type (topSub-rename a t)
  topSub-rename a (tm-effect_pure t) = cong tm-effect_pure (topSub-rename a t)
  topSub-rename a (tm-effect_bind e k) = cong₂ tm-effect_bind (topSub-rename a e) (topSub-rename a k)
  topSub-rename a (tm-hole n) = refl
  topSub-rename a (tm-absurd) = refl

  -- The binder case of `topSub-rename`: the extended substitution is
  -- inverse to the extended weakening.
  topSub-rename-binder : ∀ a t
    → substS (extSub (topSub a)) (rename (ext wk) t) ≡ t
  topSub-rename-binder a t =
    trans (subst-rename (extSub (topSub a)) (ext wk) t)
          (trans (cong (λ σ → substS σ t)
                       (funext (λ k → extSub^-topSub-ext^-wk 1 a k)))
                 (substS-idSub t))

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



-- `renameTerms (ext^ ar ρ) (branch-field-vars ar) ≡ branch-field-vars ar`.
renameTerms-field-vars : ∀ ar (ρ : Ren)
  → renameTerms (ext^ ar ρ) (branch-field-vars ar) ≡ branch-field-vars ar
renameTerms-field-vars ar ρ =
  trans (renameTerms-map (ext^ ar ρ) (branch-field-vars ar))
        (trans (cong (map (rename (ext^ ar ρ))) (sym (map-tm-var-upto ar)))
               (trans (map-compose (rename (ext^ ar ρ)) tm-var (upto ar))
                      (trans (map-upto-fix ar ar ρ (≤-refl {ar}))
                              (sym (map-tm-var-upto ar)))))
  where
    map-tm-var-upto : ∀ ar → branch-field-vars ar ≡ map tm-var (upto ar)
    map-tm-var-upto ar = refl

    map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (f ∘ g) xs
    map-compose f g [] = refl
    map-compose f g (x ∷ xs) = cong₂ _∷_ refl (map-compose f g xs)

    -- `map f (upto ar) ≡ map g (upto ar)` when `f` and `g` agree below `ar`.
    map-upto-cong : ∀ ar {f g : ℕ → Term} → (∀ k → k < ar → f k ≡ g k)
      → map f (upto ar) ≡ map g (upto ar)
    map-upto-cong zero h = refl
    map-upto-cong (suc ar) h =
      cong₂ _∷_ (h 0 (s≤s z≤n))
            (trans (map-compose _ suc (upto ar))
                   (trans (map-upto-cong ar (λ k p → h (suc k) (s≤s p)))
                          (sym (map-compose _ suc (upto ar)))))

    -- `map (λ k → tm-var (ext^ n ρ k)) (upto ar) ≡ map tm-var (upto ar)`
    -- when `ar ≤ n`: every field index (`< ar ≤ n`) is fixed by `ext^ n ρ`.
    map-upto-fix : ∀ ar n (ρ : Ren) → ar ≤ n
      → map (λ k → tm-var (ext^ n ρ k)) (upto ar) ≡ map tm-var (upto ar)
    map-upto-fix ar n ρ le =
      map-upto-cong ar (λ k p → cong tm-var (ext^-fix n ρ k (≤-trans p le)))

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
        (trans (cong (map (substS (extSub^ ar σ))) (sym (map-tm-var-upto ar)))
               (trans (map-compose (substS (extSub^ ar σ)) tm-var (upto ar))
                      (trans (map-upto-subst-fix ar ar σ (≤-refl {ar}))
                             (sym (map-tm-var-upto ar)))))
  where
    map-tm-var-upto : ∀ ar → branch-field-vars ar ≡ map tm-var (upto ar)
    map-tm-var-upto ar = refl

    map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (f ∘ g) xs
    map-compose f g [] = refl
    map-compose f g (x ∷ xs) = cong₂ _∷_ refl (map-compose f g xs)

    -- `map f (upto ar) ≡ map g (upto ar)` when `f` and `g` agree below `ar`.
    map-upto-cong : ∀ ar {f g : ℕ → Term} → (∀ k → k < ar → f k ≡ g k)
      → map f (upto ar) ≡ map g (upto ar)
    map-upto-cong zero h = refl
    map-upto-cong (suc ar) h =
      cong₂ _∷_ (h 0 (s≤s z≤n))
            (trans (map-compose _ suc (upto ar))
                   (trans (map-upto-cong ar (λ k p → h (suc k) (s≤s p)))
                          (sym (map-compose _ suc (upto ar)))))

    map-upto-subst-fix : ∀ ar n σ → ar ≤ n
      → map (λ k → substS (extSub^ n σ) (tm-var k)) (upto ar) ≡ map tm-var (upto ar)
    map-upto-subst-fix ar n σ le =
      map-upto-cong ar (λ k p → substS-extSub^-fix n σ k (≤-trans p le))

-- The branch motive under a substitution.
subst-branch-motive : ∀ ar σ (m : Term) (cn : Name)
  → substS (extSub^ ar σ) (tm-app (rename (λ j → j + ar) m) (tm-ctor cn (branch-field-vars ar)))
  ≡ tm-app (rename (λ j → j + ar) (substS σ m)) (tm-ctor cn (branch-field-vars ar))
subst-branch-motive ar σ m cn =
  cong₂ tm-app
        (subst-extSub^-shift ar σ m)
        (cong (tm-ctor cn) (substTerms-field-vars ar σ))

------------------------------------------------------------------------
-- Substitution commutes with the branch-field substitution `argsSub`.
--
-- `substArgs args b = substS (argsSub args) b` substitutes the constructor's
-- fields into a branch body. Substituting the WHOLE thing by `σ` is the same
-- as substituting the (σ-substituted) fields and applying `σ` only to the
-- body's NON-field variables (via the `length args`-fold extension
-- `extSub^ (length args) σ`):
--
--   substS σ (substArgs args b)
--     ≡ substArgs (map (substS σ) args) (substS (extSub^ (length args) σ) b)
--
-- This is the law the ι case of the confluence development's substitution
-- commutation lemma needs.
------------------------------------------------------------------------

tailOf : List Term → List Term
tailOf [] = []
tailOf (x ∷ xs) = xs

-- `argsSub args ∘s shiftRen (length args) 0` is the identity substitution:
-- the shift maps every index into the "base environment" region, which
-- `argsSub` maps back to a variable.
argsSub-shift : ∀ (args : List Term) j
  → (argsSub args ∘s shiftRen (length args) 0) j ≡ tm-var j
argsSub-shift args j =
  trans (cong (argsSub args) (+-comm j (length args)))
        (argsSub-go-raise 0 args j)

-- `substS (argsSub args) (rename (shiftRen (length args) 0) t) ≡ t`.
substS-argsSub-shift : ∀ (args : List Term) t
  → substS (argsSub args) (rename (shiftRen (length args) 0) t) ≡ t
substS-argsSub-shift args t =
  trans (subst-rename (argsSub args) (shiftRen (length args) 0) t)
        (trans (cong (λ σ → substS σ t) (funext (argsSub-shift args)))
               (substS-idSub t))

-- `substS (argsSub xs) (rename wk t) ≡ substS (argsSub (tailOf xs)) t` for a
-- non-empty `xs`: the `wk` shift moves every variable into the field region,
-- which `argsSub` maps back down.
substS-argsSub-wk : ∀ (x : Term) (xs : List Term) t
  → substS (argsSub (x ∷ xs)) (rename wk t) ≡ substS (argsSub xs) t
substS-argsSub-wk x xs t =
  trans (subst-rename (argsSub (x ∷ xs)) wk t)
        (cong (λ τ → substS τ t) (funext (λ j → refl)))

-- `substS σ (argsSub args k) ≡ substS (argsSub (map (substS σ) args)) (extSub^ (length args) σ k)`.
subst-argsSub-coh : ∀ σ (args : List Term) k
  → substS σ (argsSub args k)
  ≡ substS (argsSub (substTermsS σ args)) (extSub^ (length args) σ k)
subst-argsSub-coh σ [] k = sym (substS-idSub (σ k))
subst-argsSub-coh σ (a ∷ args) zero = refl
subst-argsSub-coh σ (a ∷ args) (suc k) =
  trans (subst-argsSub-coh σ args k)
        (sym (subst-argsSub-suc σ a args k))
  where
    -- The `suc` step: `extSub^`'s extension matches `argsSub`'s tail.
    subst-argsSub-suc : ∀ σ (a : Term) (args : List Term) k
      → substS (argsSub (substTermsS σ (a ∷ args))) (extSub^ (length (a ∷ args)) σ (suc k))
      ≡ substS (argsSub (substTermsS σ args)) (extSub^ (length args) σ k)
    subst-argsSub-suc σ a args k =
      substS-argsSub-wk (substS σ a) (substTermsS σ args) (extSub^ (length args) σ k)

-- `substS σ (substArgs args b) ≡ substArgs (map (substS σ) args) (substS (extSub^ (length args) σ) b)`.
subst-prefix : ∀ σ args b
  → substS σ (substS (argsSub args) b)
  ≡ substS (argsSub (substTermsS σ args)) (substS (extSub^ (length args) σ) b)
subst-prefix σ args b =
  trans (subst-compose σ (argsSub args) b)
        (trans (cong (λ τ → substS τ b) (funext (subst-argsSub-coh σ args)))
               (sym (subst-compose (argsSub (substTermsS σ args)) (extSub^ (length args) σ) b)))


------------------------------------------------------------------------
-- Renaming commutes with the branch-field substitution `argsSub`.
--
-- `rename ρ (substArgs args b) ≡ substArgs (renameTerms ρ args) (rename (ext^ (length args) ρ) b)`.
-- The proof is the `rename`-analogue of `subst-argsSub`: the two composed
-- renamings agree pointwise.
------------------------------------------------------------------------

rename-argsSub-coh : ∀ ρ args k
  → rename ρ (argsSub args k)
  ≡ argsSub (renameTerms ρ args) (ext^ (length args) ρ k)
rename-argsSub-coh ρ [] k = refl
rename-argsSub-coh ρ (a ∷ args) zero = refl
rename-argsSub-coh ρ (a ∷ args) (suc k) = rename-argsSub-coh ρ args k

rename-prefix : ∀ ρ args b
  → rename ρ (substS (argsSub args) b)
  ≡ substS (argsSub (renameTerms ρ args)) (rename (ext^ (length args) ρ) b)
rename-prefix ρ args b =
  trans (rename-subst ρ (argsSub args) b)
        (trans (cong (λ τ → substS τ b) (funext (rename-argsSub-coh ρ args)))
               (sym (subst-rename (argsSub (renameTerms ρ args)) (ext^ (length args) ρ) b)))

-- Structural maps commute with list reversal.
renameTerms-reverse : ∀ ρ xs → renameTerms ρ (reverse xs) ≡ reverse (renameTerms ρ xs)
renameTerms-reverse ρ xs =
  trans (renameTerms-map ρ (reverse xs))
    (trans (reverse-map (rename ρ) xs) (cong reverse (sym (renameTerms-map ρ xs))))

substTerms-reverse : ∀ σ xs → substTermsS σ (reverse xs) ≡ reverse (substTermsS σ xs)
substTerms-reverse σ xs =
  trans (substTerms-map σ (reverse xs))
    (trans (reverse-map (substS σ) xs) (cong reverse (sym (substTerms-map σ xs))))

-- Surface-order iota substitution, unlike an already ordered local prefix.
subst-argsSub : ∀ σ args b → substS σ (substArgs args b)
  ≡ substArgs (substTermsS σ args) (substS (extSub^ (length args) σ) b)
subst-argsSub σ args b =
  trans (subst-prefix σ (reverse args) b)
    (trans (cong (λ xs → substS (argsSub xs) (substS (extSub^ (length (reverse args)) σ) b))
      (substTerms-reverse σ args))
      (cong (λ n → substS (argsSub (reverse (substTermsS σ args))) (substS (extSub^ n σ) b))
        (length-reverse args)))

rename-substArgs : ∀ ρ args b → rename ρ (substArgs args b)
  ≡ substArgs (renameTerms ρ args) (rename (ext^ (length args) ρ) b)
rename-substArgs ρ args b =
  trans (rename-prefix ρ (reverse args) b)
    (trans (cong (λ xs → substS (argsSub xs) (rename (ext^ (length (reverse args)) ρ) b))
      (renameTerms-reverse ρ args))
      (cong (λ n → substS (argsSub (reverse (renameTerms ρ args))) (rename (ext^ n ρ) b))
        (length-reverse args)))

rename-surface-fields : ∀ ar ρ
  → renameTerms (ext^ ar ρ) (surface-field-vars ar) ≡ surface-field-vars ar
rename-surface-fields ar ρ =
  trans (renameTerms-reverse (ext^ ar ρ) (branch-field-vars ar))
    (cong reverse (renameTerms-field-vars ar ρ))

subst-surface-fields : ∀ ar σ
  → substTermsS (extSub^ ar σ) (surface-field-vars ar) ≡ surface-field-vars ar
subst-surface-fields ar σ =
  trans (substTerms-reverse (extSub^ ar σ) (branch-field-vars ar))
    (cong reverse (substTerms-field-vars ar σ))

rename-surface-motive : ∀ ar ρ m cn
  → rename (ext^ ar ρ)
      (tm-app (rename (λ j → j + ar) m) (tm-ctor cn (surface-field-vars ar)))
    ≡ tm-app (rename (λ j → j + ar) (rename ρ m)) (tm-ctor cn (surface-field-vars ar))
rename-surface-motive ar ρ m cn =
  cong₂ tm-app (sym (rename-raise ar ρ m)) (cong (tm-ctor cn) (rename-surface-fields ar ρ))

subst-surface-motive : ∀ ar σ m cn
  → substS (extSub^ ar σ)
      (tm-app (rename (λ j → j + ar) m) (tm-ctor cn (surface-field-vars ar)))
    ≡ tm-app (rename (λ j → j + ar) (substS σ m)) (tm-ctor cn (surface-field-vars ar))
subst-surface-motive ar σ m cn =
  cong₂ tm-app (subst-extSub^-shift ar σ m) (cong (tm-ctor cn) (subst-surface-fields ar σ))
