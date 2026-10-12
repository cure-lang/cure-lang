------------------------------------------------------------------------
-- Confluence of `_⇝_` via parallel reduction (the Tait–Martin-Löf method).
--
-- The reduction relation `_⇝_` is NOT deterministic, so confluence is not
-- immediate. The Tait–Martin-Löf method proves it via the parallel reduction
-- `_⇉_` (Core/Parallel.agda):
--
--   * `⇉-diamond` : `⇉` has the diamond property;
--   * `⇝ ⊆ ⇉` and `⇉ ⊆ ⇝*` (Core/Parallel.agda) turn the diamond into
--     confluence of `_⇝_`.
--
-- The crux of the diamond is the SUBSTITUTION COMMUTATION lemma
-- (`⇉-substS`): parallel reduction is closed under substitution. It is stated
-- MULTI-STEP (`_⇉*_`) because substituting into a neutral value can produce a
-- redex (if the substitution makes the head a lambda), so a single parallel
-- step does not suffice.
--
-- VALUE-FREENESS. `_⇉_`'s β/ζ rules carry NO `Value` side condition (unlike
-- an earlier formulation), because `_⇝_`'s β/ζ do not need one either:
-- Preservation's β case uses `check-infer` (a hole-free term that checks
-- infers its type), which needs no value structure. With the side conditions
-- gone, `⇉-substS` is the STANDARD textbook proof — there is no
-- `substS-Value-or-redex` case analysis to do, because the redex that a
-- substitution can create is handled by the redex rule itself (whose
-- argument is now unrestricted).
------------------------------------------------------------------------
module Proof.Confluence where

open import Data.Bool using (Bool; true; false)
open import Data.String.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; length; map; find; reverse)
open import Data.List using () renaming (lookup to listLookup)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax
open import Core.Signature using (just-inj)
open import Core.Reduction
import Core.Parallel as P
open import Proof.Substitution

-- The literal-peel rules' branch arities: `Z`/`First` take 0/1 fields, etc.
LiteralArity : Set
LiteralArity =
    (∀ {brs ar b} → findBranch "Z" brs ≡ just ("Z" , ar , b) → 0 ≡ ar)
  × (∀ {brs ar b} → findBranch "S" brs ≡ just ("S" , ar , b) → 1 ≡ ar)
  × (∀ {brs ar b} → findBranch "First" brs ≡ just ("First" , ar , b) → 1 ≡ ar)
  × (∀ {brs ar b} → findBranch "Next" brs ≡ just ("Next" , ar , b) → 2 ≡ ar)

-- A global's body is closed (so `substS σ` fixes it).
ClosedBody : Signature → Set
ClosedBody sig = ∀ {f body′} → Signature.body sig f ≡ just body′ → Scoped 0 body′

module Conf (sig : Signature) (la : LiteralArity) (cb : ClosedBody sig) where

  open P.Par sig public

  ------------------------------------------------------------------------
  -- The length of a `substTermsS` image.
  ------------------------------------------------------------------------

  length-substTermsS : ∀ (σ : Sub) (ts : List Term) → length (substTermsS σ ts) ≡ length ts
  length-substTermsS σ [] = refl
  length-substTermsS σ (x ∷ xs) = cong suc (length-substTermsS σ xs)

  ------------------------------------------------------------------------
  -- `⇉` commutes with renaming (purely structural).
  --
  -- With the `Value` side conditions gone, `p-rename` needs NO
  -- `Canonical`/`Neutral`/`Value` transport — it is a plain structural
  -- recursion. It is defined BEFORE the substitution lemma because the
  -- latter's `⇉-substS-refl` builds on it.
  ------------------------------------------------------------------------

  mutual
    p-rename : ∀ (ρ : Ren) {t t′} → _⇉_ t t′ → _⇉_ (rename ρ t) (rename ρ t′)
    p-rename ρ p-type = p-type
    p-rename ρ p-var = p-var
    p-rename ρ p-global = p-global
    p-rename ρ p-int_type = p-int_type
    p-rename ρ p-int_lit = p-int_lit
    p-rename ρ p-nat_lit = p-nat_lit
    p-rename ρ p-bounded_lit = p-bounded_lit
    p-rename ρ p-float_type = p-float_type
    p-rename ρ p-float_lit = p-float_lit
    p-rename ρ p-binary_type = p-binary_type
    p-rename ρ p-atom_type = p-atom_type
    p-rename ρ p-atom_lit = p-atom_lit
    p-rename ρ p-hole = p-hole
    p-rename ρ p-absurd = p-absurd
    p-rename ρ (p-pi sd sc) = p-pi (p-rename ρ sd) (p-rename (ext ρ) sc)
    p-rename ρ (p-lam sd sb) = p-lam (p-rename ρ sd) (p-rename (ext ρ) sb)
    p-rename ρ (p-let sty sv sb) = p-let (p-rename ρ sty) (p-rename ρ sv) (p-rename (ext ρ) sb)
    p-rename ρ (p-app sf sa) = p-app (p-rename ρ sf) (p-rename ρ sa)
    p-rename ρ (p-data sps sis) = p-data (p-rename-terms ρ sps) (p-rename-terms ρ sis)
    p-rename ρ (p-ctor sargs) = p-ctor (p-rename-terms ρ sargs)
    p-rename ρ (p-ctor-head sx) = p-ctor-head (p-rename ρ sx)
    p-rename ρ (p-ctor-tail st) = p-ctor-tail (p-rename ρ st)
    p-rename ρ (p-case ss sm sbs) = p-case (p-rename ρ ss) (p-rename ρ sm) (p-rename-brs ρ sbs)
    p-rename ρ (p-effect_type st) = p-effect_type (p-rename ρ st)
    p-rename ρ (p-effect_pure st) = p-effect_pure (p-rename ρ st)
    p-rename ρ (p-effect_bind se sk) = p-effect_bind (p-rename ρ se) (p-rename ρ sk)
    p-rename ρ (p-β {g} {d} {d′} {b} {b′} {a} {a′} sd sb sa) =
      subst (λ z → _⇉_ (rename ρ (tm-app (tm-lam g d b) a)) z)
            (sym (rename-topSub ρ a′ b′))
            (p-β (p-rename ρ sd) (p-rename-star (ext ρ) sb) (p-rename ρ sa))
    p-rename ρ (p-ζ {g} {ty} {ty′} {v} {v′} {b} {b′} sty sv sb) =
      subst (λ z → _⇉_ (rename ρ (tm-let g ty v b)) z)
            (sym (rename-topSub ρ v′ b′))
            (p-ζ (p-rename ρ sty) (p-rename ρ sv) (p-rename-star (ext ρ) sb))
    p-rename ρ (p-ι {m} {m′} {brs} {brs′ = brs′} {c} {ar} {b} {b′} {args} {args′}
                     found len sm sbrs sbs sargs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-ctor c args) m brs)) z)
            (sym (rename-substArgs ρ args′ b′))
            (subst (λ n → _⇉_ (rename ρ (tm-case (tm-ctor c args) m brs))
                              (substArgs (renameTerms ρ args′) (rename (ext^ n ρ) b′)))
                   (sym (trans (⇉-terms-length sargs) len))
                   (p-ι {brs′ = renameBranches ρ brs′} (findBranch-rename ρ c brs′ found)
                        (trans (length-renameTerms ρ args) len)
                        (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ ar ρ) sbs)
                        (p-rename-terms ρ sargs)))
    p-rename ρ (p-ι-nat-zero {m} {m′} {brs} {brs′ = brs′} {ar} {b} {b′} found sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-nat_lit 0) m brs)) z)
            (sym (rename-substArgs ρ [] b′))
            (subst (λ n → _⇉_ (rename ρ (tm-case (tm-nat_lit 0) m brs))
                              (substArgs [] (rename (ext^ n ρ) b′)))
                   (sym (la-Z {brs = renameBranches ρ brs′} (findBranch-rename ρ "Z" brs′ found)))
                   (p-ι-nat-zero {brs = renameBranches ρ brs} {brs′ = renameBranches ρ brs′}
                                 {ar = ar} {b = rename (ext^ ar ρ) b} {b′ = rename (ext^ ar ρ) b′}
                                 (findBranch-rename ρ "Z" brs′ found)
                                 (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ ar ρ) sbs)))
      where
        la-Z : ∀ {brs} {ar} {b} → findBranch "Z" brs ≡ just ("Z" , ar , b) → 0 ≡ ar
        la-Z {brs} = proj₁ la {brs}
    p-rename ρ (p-ι-nat-suc {m} {m′} {brs} {brs′ = brs′} {ar} {b} {b′} {n} found sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-nat_lit (suc n)) m brs)) z)
            (sym (rename-substArgs ρ (tm-nat_lit n ∷ []) b′))
            (subst (λ m′ → _⇉_ (rename ρ (tm-case (tm-nat_lit (suc n)) m brs))
                               (substArgs (tm-nat_lit n ∷ []) (rename (ext^ m′ ρ) b′)))
                   (sym (la-S {brs = renameBranches ρ brs′} (findBranch-rename ρ "S" brs′ found)))
                   (p-ι-nat-suc {brs = renameBranches ρ brs} {brs′ = renameBranches ρ brs′}
                                {ar = ar} {b = rename (ext^ ar ρ) b} {b′ = rename (ext^ ar ρ) b′}
                                (findBranch-rename ρ "S" brs′ found)
                                (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ ar ρ) sbs)))
      where
        la-S : ∀ {brs} {ar} {b} → findBranch "S" brs ≡ just ("S" , ar , b) → 1 ≡ ar
        la-S {brs} = proj₁ (proj₂ la) {brs}
    p-rename ρ (p-ι-bounded-zero {m} {m′} {brs} {brs′ = brs′} {ar} {b} {b′} found sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-bounded_lit 0) m brs)) z)
            (sym (rename-substArgs ρ (tm-nat_lit 0 ∷ []) b′))
            (subst (λ m′ → _⇉_ (rename ρ (tm-case (tm-bounded_lit 0) m brs))
                               (substArgs (tm-nat_lit 0 ∷ []) (rename (ext^ m′ ρ) b′)))
                   (sym (la-First {brs = renameBranches ρ brs′} (findBranch-rename ρ "First" brs′ found)))
                   (p-ι-bounded-zero {brs = renameBranches ρ brs} {brs′ = renameBranches ρ brs′}
                                     {ar = ar} {b = rename (ext^ ar ρ) b} {b′ = rename (ext^ ar ρ) b′}
                                     (findBranch-rename ρ "First" brs′ found)
                                     (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ ar ρ) sbs)))
      where
        la-First : ∀ {brs} {ar} {b} → findBranch "First" brs ≡ just ("First" , ar , b) → 1 ≡ ar
        la-First {brs} = proj₁ (proj₂ (proj₂ la)) {brs}
    p-rename ρ (p-ι-bounded-suc {m} {m′} {brs} {brs′ = brs′} {ar} {b} {b′} {k} found sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-bounded_lit (suc k)) m brs)) z)
            (sym (rename-substArgs ρ (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b′))
            (subst (λ m′ → _⇉_ (rename ρ (tm-case (tm-bounded_lit (suc k)) m brs))
                               (substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) (rename (ext^ m′ ρ) b′)))
                   (sym (la-Next {brs = renameBranches ρ brs′} (findBranch-rename ρ "Next" brs′ found)))
                   (p-ι-bounded-suc {brs = renameBranches ρ brs} {brs′ = renameBranches ρ brs′}
                                    {ar = ar} {b = rename (ext^ ar ρ) b} {b′ = rename (ext^ ar ρ) b′}
                                    (findBranch-rename ρ "Next" brs′ found)
                                    (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ ar ρ) sbs)))
      where
        la-Next : ∀ {brs} {ar} {b} → findBranch "Next" brs ≡ just ("Next" , ar , b) → 2 ≡ ar
        la-Next {brs} = proj₂ (proj₂ (proj₂ la)) {brs}
    p-rename ρ (p-δ eq) = subst (λ z → _⇉_ (tm-global _) z) (sym (rename-closed (cb eq))) (p-δ eq)

    p-rename-terms : ∀ (ρ : Ren) {ts ts′} → _⇉*ᵗ_ ts ts′ → _⇉*ᵗ_ (renameTerms ρ ts) (renameTerms ρ ts′)
    p-rename-terms ρ ⇉*-nil = ⇉*-nil
    p-rename-terms ρ (⇉*-cons sx sxs) = ⇉*-cons (p-rename ρ sx) (p-rename-terms ρ sxs)

    p-rename-brs : ∀ (ρ : Ren) {bs bs′} → _⇉*ᵇ_ bs bs′ → _⇉*ᵇ_ (renameBranches ρ bs) (renameBranches ρ bs′)
    p-rename-brs ρ ⇉ᵇ-nil = ⇉ᵇ-nil
    p-rename-brs ρ (⇉ᵇ-cons {ar = ar} sbs sbs′) =
      ⇉ᵇ-cons (p-rename-star (ext^ ar ρ) sbs) (p-rename-brs ρ sbs′)

    p-rename-star : ∀ (ρ : Ren) {t t′} → _⇉*_ t t′ → _⇉*_ (rename ρ t) (rename ρ t′)
    p-rename-star ρ ⇉*-refl = ⇉*-refl
    p-rename-star ρ (⇉*-step s ss) = ⇉*-step (p-rename ρ s) (p-rename-star ρ ss)

    length-renameTerms : ∀ (ρ : Ren) (xs : List Term) → length (renameTerms ρ xs) ≡ length xs
    length-renameTerms ρ [] = refl
    length-renameTerms ρ (x ∷ xs) = cong suc (length-renameTerms ρ xs)

  ------------------------------------------------------------------------
  -- `⇉` commutes with the substitution extensions.
  ------------------------------------------------------------------------

  ⇉-extSub : ∀ {σ σ′} → (∀ k → _⇉_ (σ k) (σ′ k))
           → ∀ k → _⇉_ (extSub σ k) (extSub σ′ k)
  ⇉-extSub h zero = p-var
  ⇉-extSub h (suc k) = p-rename wk (h k)

  ⇉-extSub^ : ∀ ar {σ σ′} → (∀ k → _⇉_ (σ k) (σ′ k))
            → ∀ k → _⇉_ (extSub^ ar σ k) (extSub^ ar σ′ k)
  ⇉-extSub^ zero h = h
  ⇉-extSub^ (suc ar) h = ⇉-extSub (⇉-extSub^ ar h)

  ------------------------------------------------------------------------
  -- Substitution commutation (multi-step).
  ------------------------------------------------------------------------

  -- The `⇉-refl` case of the substitution lemma: pushing a substitution
  -- through a term is a multi-step parallel reduction. This is a PURE
  -- structural recursion on the TERM (no redex can be created, because no
  -- rule fires), so it does not participate in the `⇉-substS` mutual
  -- recursion — which is what makes the termination structural.
  mutual
    ⇉-substS-refl : ∀ (σ σ′ : Sub) → (∀ k → _⇉_ (σ k) (σ′ k)) → ∀ t
                  → _⇉*_ (substS σ t) (substS σ′ t)
    ⇉-substS-refl σ σ′ h (tm-type l) = ⇉*-step p-type ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-var k) = ⇉*-step (h k) ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-pi g d c) =
      ⇉*-trans (⇉*-pi-dom (⇉-substS-refl σ σ′ h d))
               (⇉*-pi-cod (⇉-substS-refl (extSub σ) (extSub σ′) (⇉-extSub h) c))
    ⇉-substS-refl σ σ′ h (tm-lam g d b) =
      ⇉*-trans (⇉*-lam-dom (⇉-substS-refl σ σ′ h d))
               (⇉*-lam-body (⇉-substS-refl (extSub σ) (extSub σ′) (⇉-extSub h) b))
    ⇉-substS-refl σ σ′ h (tm-let g ty v b) =
      ⇉*-trans (⇉*-let-ty (⇉-substS-refl σ σ′ h ty))
        (⇉*-trans (⇉*-let-val (⇉-substS-refl σ σ′ h v))
                  (⇉*-let-body (⇉-substS-refl (extSub σ) (extSub σ′) (⇉-extSub h) b)))
    ⇉-substS-refl σ σ′ h (tm-app f a) =
      ⇉*-trans (⇉*-app₁ (⇉-substS-refl σ σ′ h f)) (⇉*-app₂ (⇉-substS-refl σ σ′ h a))
    ⇉-substS-refl σ σ′ h (tm-data n ps is) =
      ⇉*-trans (⇉*-data-params* [] _ _ _ (⇉-substS-refl-terms σ σ′ h ps))
               (⇉*-data-indices* [] _ _ _ (⇉-substS-refl-terms σ σ′ h is))
    ⇉-substS-refl σ σ′ h (tm-ctor n args) =
      ⇉*-ctor* [] _ _ (⇉-substS-refl-terms σ σ′ h args)
    ⇉-substS-refl σ σ′ h (tm-case s m brs) =
      ⇉*-trans (⇉*-case (⇉-substS-refl σ σ′ h s))
        (⇉*-trans (⇉*-case-motive (⇉-substS-refl σ σ′ h m))
                  (⇉*-case-brs (⇉-substBranchesS-refl σ σ′ h brs)))
    ⇉-substS-refl σ σ′ h (tm-global n) = ⇉*-step p-global ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-int_type) = ⇉*-step p-int_type ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-int_lit k) = ⇉*-step p-int_lit ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-nat_lit k) = ⇉*-step p-nat_lit ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-bounded_lit k) = ⇉*-step p-bounded_lit ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-float_type) = ⇉*-step p-float_type ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-float_lit) = ⇉*-step p-float_lit ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-binary_type) = ⇉*-step p-binary_type ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-atom_type) = ⇉*-step p-atom_type ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-atom_lit n) = ⇉*-step p-atom_lit ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-effect_type t) = ⇉*-effect_type (⇉-substS-refl σ σ′ h t)
    ⇉-substS-refl σ σ′ h (tm-effect_pure t) = ⇉*-effect_pure (⇉-substS-refl σ σ′ h t)
    ⇉-substS-refl σ σ′ h (tm-effect_bind e k) =
      ⇉*-trans (⇉*-effect_bind₁ (⇉-substS-refl σ σ′ h e)) (⇉*-effect_bind₂ (⇉-substS-refl σ σ′ h k))
    ⇉-substS-refl σ σ′ h (tm-hole n) = ⇉*-step p-hole ⇉*-refl
    ⇉-substS-refl σ σ′ h (tm-absurd) = ⇉*-step p-absurd ⇉*-refl

    ⇉-substS-refl-terms : ∀ (σ σ′ : Sub) → (∀ k → _⇉_ (σ k) (σ′ k)) → ∀ ts
                        → _⇉*ᵗ*_ (substTermsS σ ts) (substTermsS σ′ ts)
    ⇉-substS-refl-terms σ σ′ h [] = ⇉ᵗ*-nil
    ⇉-substS-refl-terms σ σ′ h (x ∷ xs) =
      ⇉ᵗ*-cons (⇉-substS-refl σ σ′ h x) (⇉-substS-refl-terms σ σ′ h xs)

    ⇉-substBranchesS-refl : ∀ (σ σ′ : Sub) → (∀ k → _⇉_ (σ k) (σ′ k)) → ∀ bs
                          → _⇉*ᵇ_ (substBranchesS σ bs) (substBranchesS σ′ bs)
    ⇉-substBranchesS-refl σ σ′ h [] = ⇉ᵇ-nil
    ⇉-substBranchesS-refl σ σ′ h ((cn , ar , b) ∷ bs) =
      ⇉ᵇ-cons (⇉-substS-refl (extSub^ ar σ) (extSub^ ar σ′) (⇉-extSub^ ar h) b)
              (⇉-substBranchesS-refl σ σ′ h bs)

  mutual
    ⇉-substS : ∀ {t t′} (σ σ′ : Sub)
             → (∀ k → _⇉_ (σ k) (σ′ k))
             → _⇉_ t t′
             → _⇉*_ (substS σ t) (substS σ′ t′)
    ⇉-substS σ σ′ h p-type = ⇉*-step p-type ⇉*-refl
    ⇉-substS σ σ′ h (p-var {k}) = ⇉*-step (h k) ⇉*-refl
    ⇉-substS σ σ′ h p-global = ⇉*-step p-global ⇉*-refl
    ⇉-substS σ σ′ h p-int_type = ⇉*-step p-int_type ⇉*-refl
    ⇉-substS σ σ′ h p-int_lit = ⇉*-step p-int_lit ⇉*-refl
    ⇉-substS σ σ′ h p-nat_lit = ⇉*-step p-nat_lit ⇉*-refl
    ⇉-substS σ σ′ h p-bounded_lit = ⇉*-step p-bounded_lit ⇉*-refl
    ⇉-substS σ σ′ h p-float_type = ⇉*-step p-float_type ⇉*-refl
    ⇉-substS σ σ′ h p-float_lit = ⇉*-step p-float_lit ⇉*-refl
    ⇉-substS σ σ′ h p-binary_type = ⇉*-step p-binary_type ⇉*-refl
    ⇉-substS σ σ′ h p-atom_type = ⇉*-step p-atom_type ⇉*-refl
    ⇉-substS σ σ′ h p-atom_lit = ⇉*-step p-atom_lit ⇉*-refl
    ⇉-substS σ σ′ h p-hole = ⇉*-step p-hole ⇉*-refl
    ⇉-substS σ σ′ h p-absurd = ⇉*-step p-absurd ⇉*-refl
    ⇉-substS σ σ′ h (p-pi sd sc) =
      ⇉*-trans (⇉*-pi-dom (⇉-substS σ σ′ h sd))
               (⇉*-pi-cod (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sc))
    ⇉-substS σ σ′ h (p-lam sd sb) =
      ⇉*-trans (⇉*-lam-dom (⇉-substS σ σ′ h sd))
               (⇉*-lam-body (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sb))
    ⇉-substS σ σ′ h (p-let sty sv sb) =
      ⇉*-trans (⇉*-let-ty (⇉-substS σ σ′ h sty))
        (⇉*-trans (⇉*-let-val (⇉-substS σ σ′ h sv))
                  (⇉*-let-body (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sb)))
    ⇉-substS σ σ′ h (p-app sf sa) =
      ⇉*-trans (⇉*-app₁ (⇉-substS σ σ′ h sf)) (⇉*-app₂ (⇉-substS σ σ′ h sa))
    ⇉-substS σ σ′ h (p-data sps sis) =
      ⇉*-trans (⇉*-data-params* [] _ _ _ (⇉-substS-terms σ σ′ h sps))
               (⇉*-data-indices* [] _ _ _ (⇉-substS-terms σ σ′ h sis))
    ⇉-substS σ σ′ h (p-ctor sargs) = ⇉*-ctor* [] _ _ (⇉-substS-terms σ σ′ h sargs)
    ⇉-substS σ σ′ h (p-ctor-head {x = x} {x′ = x′} {xs = xs} sx) =
      ⇉*-ctor* [] _ _ (⇉ᵗ*-cons (⇉-substS σ σ′ h sx) (⇉-substS-terms-refl σ σ′ xs h))
    ⇉-substS σ σ′ h (p-ctor-tail {x = x} {xs = xs} {xs′ = xs′} st) =
      ⇉*-ctor* [] _ _ (⇉ᵗ*-cons (⇉-substS-refl σ σ′ h x) (⇉-substS-ctor-tail* σ σ′ h st))
    ⇉-substS σ σ′ h (p-case ss sm sbs) =
      ⇉*-trans (⇉*-case (⇉-substS σ σ′ h ss))
        (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
                  (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbs)))
    ⇉-substS σ σ′ h (p-effect_type st) = ⇉*-effect_type (⇉-substS σ σ′ h st)
    ⇉-substS σ σ′ h (p-effect_pure st) = ⇉*-effect_pure (⇉-substS σ σ′ h st)
    ⇉-substS σ σ′ h (p-effect_bind se sk) =
      ⇉*-trans (⇉*-effect_bind₁ (⇉-substS σ σ′ h se)) (⇉*-effect_bind₂ (⇉-substS σ σ′ h sk))
    ⇉-substS σ σ′ h (p-β {g} {d} {d′} {b} {b′} {a} {a′} sd sb sa) =
      subst (λ z → _⇉*_ (substS σ (tm-app (tm-lam g d b) a)) z)
            (sym (subst-topSub σ′ a′ b′))
            (⇉*-trans (⇉*-app₂ (⇉-substS σ σ′ h sa))
              (⇉*-trans (⇉*-app₁ (⇉*-trans (⇉*-lam-dom (⇉-substS σ σ′ h sd))
                                            (⇉*-lam-body (⇉-substS-star (extSub σ) (extSub σ′)
                                                                        (⇉-extSub h) sb))))
                        (⇉*-step (p-β (⇉-refl _) ⇉*-refl (⇉-refl _)) ⇉*-refl)))
    ⇉-substS σ σ′ h (p-ζ {g} {ty} {ty′} {v} {v′} {b} {b′} sty sv sb) =
      subst (λ z → _⇉*_ (substS σ (tm-let g ty v b)) z)
            (sym (subst-topSub σ′ v′ b′))
            (⇉*-trans (⇉*-let-ty (⇉-substS σ σ′ h sty))
              (⇉*-trans (⇉*-let-val (⇉-substS σ σ′ h sv))
                (⇉*-trans (⇉*-let-body (⇉-substS-star (extSub σ) (extSub σ′)
                                                       (⇉-extSub h) sb))
                          (⇉*-step (p-ζ (⇉-refl _) (⇉-refl _) ⇉*-refl) ⇉*-refl))))
    ⇉-substS σ σ′ h (p-ι {m} {m′} {brs} {brs′} {c} {ar} {b} {b′} {args} {args′}
                         found len sm sbrs sbs sargs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-ctor c args) m brs)) z)
            (sym (subst-argsSub σ′ args′ b′))
            (subst (λ n → _⇉*_ (substS σ (tm-case (tm-ctor c args) m brs))
                                (substArgs (substTermsS σ′ args′) (substS (extSub^ n σ′) b′)))
                   (sym (trans (⇉-terms-length sargs) len))
                   (⇉*-trans (⇉*-case (⇉*-ctor* [] _ _ (⇉-substS-terms σ σ′ h sargs)))
                     (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
                       (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                         (⇉*-step (p-ι {brs = substBranchesS σ′ brs′} {brs′ = substBranchesS σ′ brs′}
                                        (findBranch-substBranchesS σ′ c brs′ found)
                                        (trans (length-substTermsS σ′ args′) (trans (⇉-terms-length sargs) len))
                                        (⇉-refl _) (⇉-refl-brs (substBranchesS σ′ brs′))
                                        (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′)
                                                       (⇉-extSub^ ar h) sbs)
                                        (⇉-refl-terms (substTermsS σ′ args′)))
                                   ⇉*-refl)))))
    ⇉-substS σ σ′ h (p-ι-nat-zero {m} {m′} {brs} {brs′} {ar} {b} {b′} found sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-nat_lit 0) m brs)) z)
            (sym (subst-argsSub σ′ [] b′))
            (subst (λ n → _⇉*_ (substS σ (tm-case (tm-nat_lit 0) m brs))
                                (substArgs [] (substS (extSub^ n σ′) b′)))
                   (sym (la-Z {brs = substBranchesS σ′ brs′} (findBranch-substBranchesS σ′ "Z" brs′ found)))
                   (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
                     (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                       (⇉*-step (p-ι-nat-zero {brs = substBranchesS σ′ brs′}
                                               {brs′ = substBranchesS σ′ brs′}
                                               (findBranch-substBranchesS σ′ "Z" brs′ found)
                                               (⇉-refl _)
                                               (⇉-refl-brs (substBranchesS σ′ brs′))
                                               (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′)
                                                              (⇉-extSub^ ar h) sbs))
                                 ⇉*-refl))))
      where
        la-Z : ∀ {brs} {ar} {b} → findBranch "Z" brs ≡ just ("Z" , ar , b) → 0 ≡ ar
        la-Z {brs} = proj₁ la {brs}
    ⇉-substS σ σ′ h (p-ι-nat-suc {m} {m′} {brs} {brs′} {ar} {b} {b′} {n} found sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-nat_lit (suc n)) m brs)) z)
            (sym (subst-argsSub σ′ (tm-nat_lit n ∷ []) b′))
            (subst (λ k → _⇉*_ (substS σ (tm-case (tm-nat_lit (suc n)) m brs))
                                (substArgs (tm-nat_lit n ∷ []) (substS (extSub^ k σ′) b′)))
                   (sym (la-S {brs = substBranchesS σ′ brs′} (findBranch-substBranchesS σ′ "S" brs′ found)))
                   (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
                     (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                       (⇉*-step (p-ι-nat-suc {brs = substBranchesS σ′ brs′}
                                              {brs′ = substBranchesS σ′ brs′}
                                              (findBranch-substBranchesS σ′ "S" brs′ found)
                                              (⇉-refl _)
                                              (⇉-refl-brs (substBranchesS σ′ brs′))
                                              (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′)
                                                             (⇉-extSub^ ar h) sbs))
                                 ⇉*-refl))))
      where
        la-S : ∀ {brs} {ar} {b} → findBranch "S" brs ≡ just ("S" , ar , b) → 1 ≡ ar
        la-S {brs} = proj₁ (proj₂ la) {brs}
    ⇉-substS σ σ′ h (p-ι-bounded-zero {m} {m′} {brs} {brs′} {ar} {b} {b′} found sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-bounded_lit 0) m brs)) z)
            (sym (subst-argsSub σ′ (tm-nat_lit 0 ∷ []) b′))
            (subst (λ k → _⇉*_ (substS σ (tm-case (tm-bounded_lit 0) m brs))
                                (substArgs (tm-nat_lit 0 ∷ []) (substS (extSub^ k σ′) b′)))
                   (sym (la-First {brs = substBranchesS σ′ brs′} (findBranch-substBranchesS σ′ "First" brs′ found)))
                   (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
                     (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                       (⇉*-step (p-ι-bounded-zero {brs = substBranchesS σ′ brs′}
                                                   {brs′ = substBranchesS σ′ brs′}
                                                   (findBranch-substBranchesS σ′ "First" brs′ found)
                                                   (⇉-refl _)
                                                   (⇉-refl-brs (substBranchesS σ′ brs′))
                                                   (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′)
                                                                  (⇉-extSub^ ar h) sbs))
                                 ⇉*-refl))))
      where
        la-First : ∀ {brs} {ar} {b} → findBranch "First" brs ≡ just ("First" , ar , b) → 1 ≡ ar
        la-First {brs} = proj₁ (proj₂ (proj₂ la)) {brs}
    ⇉-substS σ σ′ h (p-ι-bounded-suc {m} {m′} {brs} {brs′} {ar} {b} {b′} {k} found sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-bounded_lit (suc k)) m brs)) z)
            (sym (subst-argsSub σ′ (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b′))
            (subst (λ j → _⇉*_ (substS σ (tm-case (tm-bounded_lit (suc k)) m brs))
                                (substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ [])
                                           (substS (extSub^ j σ′) b′)))
                   (sym (la-Next {brs = substBranchesS σ′ brs′} (findBranch-substBranchesS σ′ "Next" brs′ found)))
                   (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
                     (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                       (⇉*-step (p-ι-bounded-suc {brs = substBranchesS σ′ brs′}
                                                  {brs′ = substBranchesS σ′ brs′}
                                                  (findBranch-substBranchesS σ′ "Next" brs′ found)
                                                  (⇉-refl _)
                                                  (⇉-refl-brs (substBranchesS σ′ brs′))
                                                  (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′)
                                                                 (⇉-extSub^ ar h) sbs))
                                 ⇉*-refl))))
      where
        la-Next : ∀ {brs} {ar} {b} → findBranch "Next" brs ≡ just ("Next" , ar , b) → 2 ≡ ar
        la-Next {brs} = proj₂ (proj₂ (proj₂ la)) {brs}
    ⇉-substS σ σ′ h (p-δ eq) =
      ⇉*-step (subst (λ z → _⇉_ (tm-global _) z) (sym (substS-closed (cb eq))) (p-δ eq)) ⇉*-refl

    -- Substitution commutes with a MULTI-step parallel reduction (by
    -- iterating the single-step lemma).
    ⇉-substS-star : ∀ {t t′} (σ σ′ : Sub)
                  → (∀ k → _⇉_ (σ k) (σ′ k))
                  → _⇉*_ t t′
                  → _⇉*_ (substS σ t) (substS σ′ t′)
    ⇉-substS-star {t = t} σ σ′ h ⇉*-refl = ⇉-substS-refl σ σ′ h t
    ⇉-substS-star σ σ′ h (⇉*-step s ss) =
      ⇉*-trans (⇉-substS σ σ′ h s)
               (⇉-substS-star σ′ σ′ (λ k → ⇉-refl _) ss)

    -- Lift a tail-ctor step into a prefix position.
    ⇉-substS-ctor-tail* : ∀ {c xs xs′} (σ σ′ : Sub)
                        → (∀ k → _⇉_ (σ k) (σ′ k))
                        → _⇉_ (tm-ctor c xs) (tm-ctor c xs′)
                        → _⇉*ᵗ*_ (substTermsS σ xs) (substTermsS σ′ xs′)
    ⇉-substS-ctor-tail* σ σ′ h (p-ctor sargs) = ⇉-substS-terms σ σ′ h sargs
    ⇉-substS-ctor-tail* σ σ′ h (p-ctor-head sx) =
      ⇉ᵗ*-cons (⇉-substS σ σ′ h sx) (⇉-substS-terms-refl σ σ′ _ h)
    ⇉-substS-ctor-tail* σ σ′ h (p-ctor-tail {x = x} {xs = ys} {xs′ = ys′} st) =
      ⇉ᵗ*-cons (⇉-substS-refl σ σ′ h x) (⇉-substS-ctor-tail* {xs = ys} {xs′ = ys′} σ σ′ h st)

    ⇉-substS-terms : ∀ {ts ts′} (σ σ′ : Sub) → (∀ k → _⇉_ (σ k) (σ′ k))
                   → _⇉*ᵗ_ ts ts′ → _⇉*ᵗ*_ (substTermsS σ ts) (substTermsS σ′ ts′)
    ⇉-substS-terms σ σ′ h ⇉*-nil = ⇉ᵗ*-nil
    ⇉-substS-terms σ σ′ h (⇉*-cons sx sxs) =
      ⇉ᵗ*-cons (⇉-substS σ σ′ h sx) (⇉-substS-terms σ σ′ h sxs)

    ⇉-substS-terms-refl : ∀ (σ σ′ : Sub) (ts : List Term) → (∀ k → _⇉_ (σ k) (σ′ k))
                        → _⇉*ᵗ*_ (substTermsS σ ts) (substTermsS σ′ ts)
    ⇉-substS-terms-refl σ σ′ [] h = ⇉ᵗ*-nil
    ⇉-substS-terms-refl σ σ′ (x ∷ xs) h =
      ⇉ᵗ*-cons (⇉-substS-refl σ σ′ h x) (⇉-substS-terms-refl σ σ′ xs h)

    ⇉-substBranchesS : ∀ {bs bs′} (σ σ′ : Sub) → (∀ k → _⇉_ (σ k) (σ′ k))
                     → _⇉*ᵇ_ bs bs′ → _⇉*ᵇ_ (substBranchesS σ bs) (substBranchesS σ′ bs′)
    ⇉-substBranchesS σ σ′ h ⇉ᵇ-nil = ⇉ᵇ-nil
    ⇉-substBranchesS σ σ′ h (⇉ᵇ-cons {ar = ar} sbs sbs′) =
      ⇉ᵇ-cons (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′) (⇉-extSub^ ar h) sbs)
              (⇉-substBranchesS σ σ′ h sbs′)
