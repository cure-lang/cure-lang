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

-- Literal-peel arities are premises of each reduction step, not a
-- hypothesis about every raw branch list. The historical impossible
-- interface is retained only in Proof.InterfaceAudit as a refutation.
-- The termination-check overrides remain separate unresolved obligations.

-- A global's body is closed (so `substS σ` fixes it).
ClosedBody : Signature → Set
ClosedBody sig = ∀ {f body′} → Signature.body sig f ≡ just body′ → Scoped 0 body′

module Conf (sig : Signature) (cb : ClosedBody sig) where

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
    p-rename ρ (p-ι-nat-zero {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} found refl sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-nat_lit 0) m brs)) z)
            (sym (rename-substArgs ρ [] b′))
            (p-ι-nat-zero (findBranch-rename ρ "Z" brs′ found) refl
              (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ 0 ρ) sbs))
    p-rename ρ (p-ι-nat-suc {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} {n = n} found refl sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-nat_lit (suc n)) m brs)) z)
            (sym (rename-substArgs ρ (tm-nat_lit n ∷ []) b′))
            (p-ι-nat-suc (findBranch-rename ρ "S" brs′ found) refl
              (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ 1 ρ) sbs))
    p-rename ρ (p-ι-bounded-zero {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} found refl sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-bounded_lit 0) m brs)) z)
            (sym (rename-substArgs ρ (tm-nat_lit 0 ∷ []) b′))
            (p-ι-bounded-zero (findBranch-rename ρ "First" brs′ found) refl
              (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ 1 ρ) sbs))
    p-rename ρ (p-ι-bounded-suc {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} {k = k} found refl sm sbrs sbs) =
      subst (λ z → _⇉_ (rename ρ (tm-case (tm-bounded_lit (suc k)) m brs)) z)
            (sym (rename-substArgs ρ (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b′))
            (p-ι-bounded-suc (findBranch-rename ρ "Next" brs′ found) refl
              (p-rename ρ sm) (p-rename-brs ρ sbrs) (p-rename-star (ext^ 2 ρ) sbs))
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
    ⇉-substS σ σ′ h (p-ι-nat-zero {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} found refl sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-nat_lit 0) m brs)) z)
            (sym (subst-argsSub σ′ [] b′))
            (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
              (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                (⇉*-step (p-ι-nat-zero {brs = substBranchesS σ′ brs′}
                                         {brs′ = substBranchesS σ′ brs′}
                                         (findBranch-substBranchesS σ′ "Z" brs′ found) refl
                                         (⇉-refl _) (⇉-refl-brs (substBranchesS σ′ brs′))
                                         (⇉-substS-star (extSub^ 0 σ) (extSub^ 0 σ′)
                                                        (⇉-extSub^ 0 h) sbs))
                          ⇉*-refl)))
    ⇉-substS σ σ′ h (p-ι-nat-suc {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} {n = n} found refl sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-nat_lit (suc n)) m brs)) z)
            (sym (subst-argsSub σ′ (tm-nat_lit n ∷ []) b′))
            (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
              (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                (⇉*-step (p-ι-nat-suc {brs = substBranchesS σ′ brs′}
                                         {brs′ = substBranchesS σ′ brs′}
                                         (findBranch-substBranchesS σ′ "S" brs′ found) refl
                                         (⇉-refl _) (⇉-refl-brs (substBranchesS σ′ brs′))
                                         (⇉-substS-star (extSub^ 1 σ) (extSub^ 1 σ′)
                                                        (⇉-extSub^ 1 h) sbs))
                          ⇉*-refl)))
    ⇉-substS σ σ′ h (p-ι-bounded-zero {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} found refl sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-bounded_lit 0) m brs)) z)
            (sym (subst-argsSub σ′ (tm-nat_lit 0 ∷ []) b′))
            (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
              (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                (⇉*-step (p-ι-bounded-zero {brs = substBranchesS σ′ brs′}
                                         {brs′ = substBranchesS σ′ brs′}
                                         (findBranch-substBranchesS σ′ "First" brs′ found) refl
                                         (⇉-refl _) (⇉-refl-brs (substBranchesS σ′ brs′))
                                         (⇉-substS-star (extSub^ 1 σ) (extSub^ 1 σ′)
                                                        (⇉-extSub^ 1 h) sbs))
                          ⇉*-refl)))
    ⇉-substS σ σ′ h (p-ι-bounded-suc {m = m} {brs = brs} {brs′ = brs′} {b′ = b′} {k = k} found refl sm sbrs sbs) =
      subst (λ z → _⇉*_ (substS σ (tm-case (tm-bounded_lit (suc k)) m brs)) z)
            (sym (subst-argsSub σ′ (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b′))
            (⇉*-trans (⇉*-case-motive (⇉-substS σ σ′ h sm))
              (⇉*-trans (⇉*-case-brs (⇉-substBranchesS σ σ′ h sbrs))
                (⇉*-step (p-ι-bounded-suc {brs = substBranchesS σ′ brs′}
                                         {brs′ = substBranchesS σ′ brs′}
                                         (findBranch-substBranchesS σ′ "Next" brs′ found) refl
                                         (⇉-refl _) (⇉-refl-brs (substBranchesS σ′ brs′))
                                         (⇉-substS-star (extSub^ 2 σ) (extSub^ 2 σ′)
                                                        (⇉-extSub^ 2 h) sbs))
                          ⇉*-refl)))
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

    -- `⇉-substS-refl` with MULTI-step hypotheses (structural on the term).
    ⇉-substS-refl* : ∀ (σ σ′ : Sub) → (∀ k → _⇉*_ (σ k) (σ′ k)) → ∀ t
                   → _⇉*_ (substS σ t) (substS σ′ t)
    ⇉-substS-refl* σ σ′ h (tm-type l) = ⇉*-step p-type ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-var k) = h k
    ⇉-substS-refl* σ σ′ h (tm-pi g d c) =
      ⇉*-trans (⇉*-pi-dom (⇉-substS-refl* σ σ′ h d))
               (⇉*-pi-cod (⇉-substS-refl* (extSub σ) (extSub σ′) (⇉-extSub*-h h) c))
    ⇉-substS-refl* σ σ′ h (tm-lam g d b) =
      ⇉*-trans (⇉*-lam-dom (⇉-substS-refl* σ σ′ h d))
               (⇉*-lam-body (⇉-substS-refl* (extSub σ) (extSub σ′) (⇉-extSub*-h h) b))
    ⇉-substS-refl* σ σ′ h (tm-let g ty v b) =
      ⇉*-trans (⇉*-let-ty (⇉-substS-refl* σ σ′ h ty))
        (⇉*-trans (⇉*-let-val (⇉-substS-refl* σ σ′ h v))
                  (⇉*-let-body (⇉-substS-refl* (extSub σ) (extSub σ′) (⇉-extSub*-h h) b)))
    ⇉-substS-refl* σ σ′ h (tm-app f a) =
      ⇉*-trans (⇉*-app₁ (⇉-substS-refl* σ σ′ h f)) (⇉*-app₂ (⇉-substS-refl* σ σ′ h a))
    ⇉-substS-refl* σ σ′ h (tm-data n ps is) =
      ⇉*-trans (⇉*-data-params* [] _ _ _ (⇉-substS-refl-terms* σ σ′ h ps))
               (⇉*-data-indices* [] _ _ _ (⇉-substS-refl-terms* σ σ′ h is))
    ⇉-substS-refl* σ σ′ h (tm-ctor n args) =
      ⇉*-ctor* [] _ _ (⇉-substS-refl-terms* σ σ′ h args)
    ⇉-substS-refl* σ σ′ h (tm-case s m brs) =
      ⇉*-trans (⇉*-case (⇉-substS-refl* σ σ′ h s))
        (⇉*-trans (⇉*-case-motive (⇉-substS-refl* σ σ′ h m))
                  (⇉*-case-brs (⇉-substBranchesS-refl* σ σ′ h brs)))
    ⇉-substS-refl* σ σ′ h (tm-global n) = ⇉*-step p-global ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-int_type) = ⇉*-step p-int_type ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-int_lit k) = ⇉*-step p-int_lit ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-nat_lit k) = ⇉*-step p-nat_lit ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-bounded_lit k) = ⇉*-step p-bounded_lit ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-float_type) = ⇉*-step p-float_type ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-float_lit) = ⇉*-step p-float_lit ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-binary_type) = ⇉*-step p-binary_type ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-atom_type) = ⇉*-step p-atom_type ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-atom_lit n) = ⇉*-step p-atom_lit ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-effect_type t) = ⇉*-effect_type (⇉-substS-refl* σ σ′ h t)
    ⇉-substS-refl* σ σ′ h (tm-effect_pure t) = ⇉*-effect_pure (⇉-substS-refl* σ σ′ h t)
    ⇉-substS-refl* σ σ′ h (tm-effect_bind e k) =
      ⇉*-trans (⇉*-effect_bind₁ (⇉-substS-refl* σ σ′ h e)) (⇉*-effect_bind₂ (⇉-substS-refl* σ σ′ h k))
    ⇉-substS-refl* σ σ′ h (tm-hole n) = ⇉*-step p-hole ⇉*-refl
    ⇉-substS-refl* σ σ′ h (tm-absurd) = ⇉*-step p-absurd ⇉*-refl

    ⇉-substS-refl-terms* : ∀ (σ σ′ : Sub) → (∀ k → _⇉*_ (σ k) (σ′ k)) → ∀ ts
                         → _⇉*ᵗ*_ (substTermsS σ ts) (substTermsS σ′ ts)
    ⇉-substS-refl-terms* σ σ′ h [] = ⇉ᵗ*-nil
    ⇉-substS-refl-terms* σ σ′ h (x ∷ xs) =
      ⇉ᵗ*-cons (⇉-substS-refl* σ σ′ h x) (⇉-substS-refl-terms* σ σ′ h xs)

    ⇉-substBranchesS-refl* : ∀ (σ σ′ : Sub) → (∀ k → _⇉*_ (σ k) (σ′ k)) → ∀ bs
                           → _⇉*ᵇ_ (substBranchesS σ bs) (substBranchesS σ′ bs)
    ⇉-substBranchesS-refl* σ σ′ h [] = ⇉ᵇ-nil
    ⇉-substBranchesS-refl* σ σ′ h ((cn , ar , b) ∷ bs) =
      ⇉ᵇ-cons (⇉-substS-refl* (extSub^ ar σ) (extSub^ ar σ′) (⇉-extSub^*-h ar h) b)
              (⇉-substBranchesS-refl* σ σ′ h bs)

    ⇉-extSub*-h : ∀ {σ σ′} → (∀ k → _⇉*_ (σ k) (σ′ k))
                → ∀ k → _⇉*_ (extSub σ k) (extSub σ′ k)
    ⇉-extSub*-h h zero = ⇉*-step p-var ⇉*-refl
    ⇉-extSub*-h h (suc k) = p-rename-star wk (h k)

    ⇉-extSub^*-h : ∀ ar {σ σ′} → (∀ k → _⇉*_ (σ k) (σ′ k))
                 → ∀ k → _⇉*_ (extSub^ ar σ k) (extSub^ ar σ′ k)
    ⇉-extSub^*-h zero h = h
    ⇉-extSub^*-h (suc ar) h = ⇉-extSub*-h (⇉-extSub^*-h ar h)

    -- `⇉-substS-star` with MULTI-step hypotheses.
    ⇉-substS-star* : ∀ {t t′} (σ σ′ : Sub)
                   → (∀ k → _⇉*_ (σ k) (σ′ k))
                   → _⇉*_ t t′
                   → _⇉*_ (substS σ t) (substS σ′ t′)
    ⇉-substS-star* {t = t} σ σ′ h ⇉*-refl = ⇉-substS-refl* σ σ′ h t
    ⇉-substS-star* σ σ′ h (⇉*-step s ss) =
      ⇉*-trans (⇉-substS σ σ (λ k → ⇉-refl _) s) (⇉-substS-star* σ σ′ h ss)

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

  ------------------------------------------------------------------------
  -- `substTopT` commutes with multi-step parallel reduction.
  --
  -- This is the lemma the diamond's β/ζ redex cases need: the argument's
  -- reduct is reached in MULTIPLE steps (`a ⇉* a′`), which the single-step
  -- hypothesis of `⇉-substS-star` cannot consume directly.
  ------------------------------------------------------------------------

  -- `topSub` commutes with a single parallel step.
  topSub-⇉ : ∀ {a a′} → _⇉_ a a′ → ∀ k → _⇉_ (topSub a k) (topSub a′ k)
  topSub-⇉ sa zero = sa
  topSub-⇉ sa (suc k) = p-var

  substTopT-⇉* : ∀ {a a′ b b′} → _⇉*_ a a′ → _⇉*_ b b′
                → _⇉*_ (substTopT a b) (substTopT a′ b′)
  substTopT-⇉* {a = a} ⇉*-refl bb =
    ⇉-substS-star (topSub a) (topSub a) (λ k → ⇉-refl _) bb
  substTopT-⇉* {a = a} {a′ = a′} {b = b} {b′ = b′} (⇉*-step {u = a″} s ss) bb =
    ⇉*-trans (⇉-substS-star (topSub a) (topSub a″) (topSub-⇉ s) bb)
             (substTopT-⇉* ss (⇉*-refl {b′}))

  -- `argsSub-go` commutes with a single-step spine reduction.
  argsSub-go-⇉ : ∀ {args args′} → _⇉*ᵗ_ args args′
               → ∀ k j → _⇉_ (argsSub-go k args j) (argsSub-go k args′ j)
  argsSub-go-⇉ ⇉*-nil k j = p-var
  argsSub-go-⇉ (⇉*-cons sx sxs) k zero = sx
  argsSub-go-⇉ (⇉*-cons sx sxs) k (suc j) = argsSub-go-⇉ sxs (suc k) j

  -- `argsSub` commutes with a single-step spine reduction.
  argsSub-⇉ : ∀ {args args′} → _⇉*ᵗ_ args args′ → ∀ k → _⇉_ (argsSub args k) (argsSub args′ k)
  argsSub-⇉ args⇉ = argsSub-go-⇉ args⇉ 0

  -- `substArgs` commutes with a single-step spine reduction and a multi-step
  -- body reduction.
  substArgs-⇉* : ∀ {args args′ b b′} → _⇉*ᵗ_ args args′ → _⇉*_ b b′
               → _⇉*_ (substArgs args b) (substArgs args′ b′)
  substArgs-⇉* {args = args} {args′ = args′} args⇉ bb =
    ⇉-substS-star (argsSub args) (argsSub args′) (argsSub-⇉ args⇉) bb

  -- `argsSub-go` commutes with a MULTI-step spine reduction (pointwise).
  argsSub-go-⇉* : ∀ {args args′} → _⇉*ᵗ*_ args args′
                → ∀ k j → _⇉*_ (argsSub-go k args j) (argsSub-go k args′ j)
  argsSub-go-⇉* ⇉ᵗ*-nil k j = ⇉*-step p-var ⇉*-refl
  argsSub-go-⇉* (⇉ᵗ*-cons sx sxs) k zero = sx
  argsSub-go-⇉* (⇉ᵗ*-cons sx sxs) k (suc j) = argsSub-go-⇉* sxs (suc k) j

  -- `substArgs` commutes with a MULTI-step spine reduction and a multi-step
  -- body reduction.
  substArgs-⇉*ᵗ* : ∀ (args args′ : List Term) {b b′} → _⇉*ᵗ*_ args args′ → _⇉*_ b b′
                  → _⇉*_ (substArgs args b) (substArgs args′ b′)
  substArgs-⇉*ᵗ* args args′ args⇉ bb =
    ⇉-substS-star* (argsSub args) (argsSub args′) (argsSub-go-⇉* args⇉ 0) bb

  -- `findBranch` is deterministic: two successful lookups of the same name
  -- in the same list agree on arity and body.
  findBranch-unique : ∀ c brs {ar b ar′ b′}
    → findBranch c brs ≡ just (c , ar , b) → findBranch c brs ≡ just (c , ar′ , b′)
    → ar ≡ ar′ × b ≡ b′
  findBranch-unique c brs e e′ with just-inj (trans (sym e) e′)
  ... | refl = refl , refl

  ctor-inj : ∀ {c ys ys′} → tm-ctor c ys ≡ tm-ctor c ys′ → ys ≡ ys′
  ctor-inj refl = refl


  -- A single ctor reduction's target is a `tm-ctor`, exposing its spine.
  ctor-of-step : ∀ {c xs u} → _⇉_ (tm-ctor c xs) u → ∃ λ ys → u ≡ tm-ctor c ys
  ctor-of-step (p-ctor {args′ = ys} sargs) = ys , refl
  ctor-of-step (p-ctor-head {x′ = x′} {xs = xs} sx) = x′ ∷ xs , refl
  ctor-of-step (p-ctor-tail {x = x} {xs′ = ys} st) = x ∷ ys , refl

  -- A ctor reduction's spine relation.
  ⇉-ctor-terms : ∀ {c xs ys} → _⇉_ (tm-ctor c xs) (tm-ctor c ys) → _⇉*ᵗ_ xs ys
  ⇉-ctor-terms (p-ctor sargs) = sargs
  ⇉-ctor-terms (p-ctor-head sx) = ⇉*-cons sx (⇉-refl-terms _)
  ⇉-ctor-terms (p-ctor-tail {x = x} st) = ⇉*-cons (⇉-refl x) (⇉-ctor-terms st)

  ⇉-ctor-terms-⇉* : ∀ {c xs ys} → _⇉_ (tm-ctor c xs) (tm-ctor c ys) → _⇉*_ (tm-ctor c xs) (tm-ctor c ys)
  ⇉-ctor-terms-⇉* s = ⇉*-step s ⇉*-refl

  -- The spine relation of a ctor reduction, packaged with its spine list and
  -- the equation identifying the target with `tm-ctor c ys`.
  ⇉-ctor-spine : ∀ {c xs s′} → _⇉_ (tm-ctor c xs) s′
               → ∃ λ ys → s′ ≡ tm-ctor c ys × _⇉*ᵗ_ xs ys
  ⇉-ctor-spine (p-ctor {args′ = ys} sargs) = ys , refl , sargs
  ⇉-ctor-spine (p-ctor-head {x′ = x′} {xs = xs} sx) = x′ ∷ xs , refl , ⇉*-cons sx (⇉-refl-terms _)
  ⇉-ctor-spine (p-ctor-tail {x = x} {xs′ = ys} st) =
    x ∷ ys , refl , ⇉*-cons (⇉-refl x)
      (subst (λ z → _⇉*ᵗ_ _ z) (sym (ctor-inj (proj₁ (proj₂ (⇉-ctor-spine st)))))
             (proj₂ (proj₂ (⇉-ctor-spine st))))

  -- The inner spine of a `p-ctor-tail` reduction, rewritten to its target.
  ctor-spine-rewrite : ∀ {c xs ys} (st : _⇉_ (tm-ctor c xs) (tm-ctor c ys))
                     → _⇉*ᵗ_ xs ys
  ctor-spine-rewrite {ys = ys} st =
    subst (λ z → _⇉*ᵗ_ _ z) (sym (ctor-inj (proj₁ (proj₂ (⇉-ctor-spine st)))))
          (proj₂ (proj₂ (⇉-ctor-spine st)))

  ------------------------------------------------------------------------
  -- The diamond property for `_⇉_` (multi-step conclusions).
  --
  -- `t ⇉ u` and `t ⇉ v` have a common reduct. The redex cases are closed by
  -- `substTopT-⇉*` / the substitution lemma; the ctor-spine cases by
  -- `⇉-diamond-ctor`.
  ------------------------------------------------------------------------

  -- Lift a multi-step ctor reduction into the tail position.
  ⇉*-ctor-tail : ∀ {c x xs xs′} → _⇉*_ (tm-ctor c xs) (tm-ctor c xs′)
               → _⇉*_ (tm-ctor c (x ∷ xs)) (tm-ctor c (x ∷ xs′))
  ⇉*-ctor-tail ⇉*-refl = ⇉*-refl
  ⇉*-ctor-tail (⇉*-step (p-ctor sargs) ss) = ⇉*-step (p-ctor-tail (p-ctor sargs)) (⇉*-ctor-tail ss)
  ⇉*-ctor-tail (⇉*-step (p-ctor-head sx) ss) = ⇉*-step (p-ctor-tail (p-ctor-head sx)) (⇉*-ctor-tail ss)
  ⇉*-ctor-tail (⇉*-step (p-ctor-tail st) ss) = ⇉*-step (p-ctor-tail (p-ctor-tail st)) (⇉*-ctor-tail ss)

  -- Termination: `⇉-diamond` recurses on the two derivations and
  -- `⇉-diamond-star` on the pair; the recursion is structurally decreasing in
  -- the derivations, but Agda cannot see it through the diamond witnesses
  -- (which are `∃`-packed). We mark the block terminating with that
  -- justification.
  {-# TERMINATING #-}
  mutual
    ⇉-diamond : ∀ {t u v} → _⇉_ t u → _⇉_ t v → ∃ λ w → _⇉*_ u w × _⇉*_ v w
    ⇉-diamond p-type p-type = _ , ⇉*-step p-type ⇉*-refl , ⇉*-step p-type ⇉*-refl
    ⇉-diamond p-var p-var = _ , ⇉*-step p-var ⇉*-refl , ⇉*-step p-var ⇉*-refl
    ⇉-diamond p-int_type p-int_type = _ , ⇉*-step p-int_type ⇉*-refl , ⇉*-step p-int_type ⇉*-refl
    ⇉-diamond p-int_lit p-int_lit = _ , ⇉*-step p-int_lit ⇉*-refl , ⇉*-step p-int_lit ⇉*-refl
    ⇉-diamond p-nat_lit p-nat_lit = _ , ⇉*-step p-nat_lit ⇉*-refl , ⇉*-step p-nat_lit ⇉*-refl
    ⇉-diamond p-bounded_lit p-bounded_lit = _ , ⇉*-step p-bounded_lit ⇉*-refl , ⇉*-step p-bounded_lit ⇉*-refl
    ⇉-diamond p-float_type p-float_type = _ , ⇉*-step p-float_type ⇉*-refl , ⇉*-step p-float_type ⇉*-refl
    ⇉-diamond p-float_lit p-float_lit = _ , ⇉*-step p-float_lit ⇉*-refl , ⇉*-step p-float_lit ⇉*-refl
    ⇉-diamond p-binary_type p-binary_type = _ , ⇉*-step p-binary_type ⇉*-refl , ⇉*-step p-binary_type ⇉*-refl
    ⇉-diamond p-atom_type p-atom_type = _ , ⇉*-step p-atom_type ⇉*-refl , ⇉*-step p-atom_type ⇉*-refl
    ⇉-diamond p-atom_lit p-atom_lit = _ , ⇉*-step p-atom_lit ⇉*-refl , ⇉*-step p-atom_lit ⇉*-refl
    ⇉-diamond p-hole p-hole = _ , ⇉*-step p-hole ⇉*-refl , ⇉*-step p-hole ⇉*-refl
    ⇉-diamond p-absurd p-absurd = _ , ⇉*-step p-absurd ⇉*-refl , ⇉*-step p-absurd ⇉*-refl
    -- global: reflexivity or δ-unfold.
    ⇉-diamond p-global p-global = _ , ⇉*-step p-global ⇉*-refl , ⇉*-step p-global ⇉*-refl
    ⇉-diamond p-global (p-δ eq) = _ , ⇉*-step (p-δ eq) ⇉*-refl , ⇉*-refl
    ⇉-diamond (p-δ eq) p-global = _ , ⇉*-refl , ⇉*-step (p-δ eq) ⇉*-refl
    ⇉-diamond {u = u} {v = v} (p-δ eq) (p-δ eq′) =
      u , ⇉*-refl , ⇉*-step (subst (λ z → _⇉_ v z) (sym (uv-eq eq eq′)) (⇉-refl v)) ⇉*-refl
      where
        uv-eq : ∀ {f u v} → Signature.body sig f ≡ just u → Signature.body sig f ≡ just v
              → u ≡ v
        uv-eq e e′ = just-inj (trans (sym e) e′)
    -- structural congruences
    ⇉-diamond (p-pi sd sc) (p-pi se sf) =
      let (d″ , dd , de) = ⇉-diamond sd se
          (c″ , cd , ce) = ⇉-diamond sc sf
      in _ , ⇉*-trans (⇉*-pi-dom dd) (⇉*-pi-cod cd) , ⇉*-trans (⇉*-pi-dom de) (⇉*-pi-cod ce)
    ⇉-diamond (p-lam sd sb) (p-lam se sf) =
      let (d″ , dd , de) = ⇉-diamond sd se
          (b″ , bd , be) = ⇉-diamond sb sf
      in _ , ⇉*-trans (⇉*-lam-dom dd) (⇉*-lam-body bd) , ⇉*-trans (⇉*-lam-dom de) (⇉*-lam-body be)
    ⇉-diamond (p-app sf sa) (p-app sf′ sa′) =
      let (f″ , fd , fe) = ⇉-diamond sf sf′
          (a″ , ad , ae) = ⇉-diamond sa sa′
      in _ , ⇉*-trans (⇉*-app₁ fd) (⇉*-app₂ ad) , ⇉*-trans (⇉*-app₁ fe) (⇉*-app₂ ae)
    ⇉-diamond (p-data sps sis) (p-data sps′ sis′) =
      let (ps″ , pd , pe) = ⇉-diamond-terms sps sps′
          (is″ , id , ie) = ⇉-diamond-terms sis sis′
      in _ , ⇉*-trans (⇉*-data-params* [] _ _ _ pd) (⇉*-data-indices* [] _ _ _ id)
           , ⇉*-trans (⇉*-data-params* [] _ _ _ pe) (⇉*-data-indices* [] _ _ _ ie)
    ⇉-diamond (p-ctor sargs) (p-ctor sargs′) =
      let (args″ , ad , ae) = ⇉-diamond-terms sargs sargs′
      in _ , ⇉*-ctor* [] _ _ ad , ⇉*-ctor* [] _ _ ae
    ⇉-diamond (p-ctor-head sx) (p-ctor-head sx′) =
      let (x″ , xd , xe) = ⇉-diamond sx sx′
      in _ , ⇉*-ctor-head xd , ⇉*-ctor-head xe
    ⇉-diamond (p-ctor-head sx) (p-ctor-tail st) =
      _ , ⇉*-step (p-ctor-tail st) ⇉*-refl , ⇉*-step (p-ctor-head sx) ⇉*-refl
    ⇉-diamond (p-ctor-tail st) (p-ctor-head sx) =
      _ , ⇉*-step (p-ctor-head sx) ⇉*-refl , ⇉*-step (p-ctor-tail st) ⇉*-refl
    ⇉-diamond {t = tm-ctor n _} (p-ctor {n = n} sargs) (p-ctor-head {n = n} {x = x} {x′ = x′} {xs = xs} sx)
      = let (ws , wd , we) = ⇉-diamond-ctor (p-ctor sargs) (p-ctor-head sx)
        in tm-ctor n ws , wd , we
    ⇉-diamond {t = tm-ctor n _} (p-ctor-head {n = n} {x = x} {x′ = x′} {xs = xs} sx) (p-ctor {n = n} sargs)
      = let (ws , wd , we) = ⇉-diamond-ctor (p-ctor-head sx) (p-ctor sargs)
        in tm-ctor n ws , wd , we
    ⇉-diamond {t = tm-ctor n _} (p-ctor {n = n} sargs) (p-ctor-tail {n = n} {x = x} st)
      = let (ws , wd , we) = ⇉-diamond-ctor (p-ctor sargs) (p-ctor-tail st)
        in tm-ctor n ws , wd , we
    ⇉-diamond {t = tm-ctor n _} (p-ctor-tail {n = n} {x = x} st) (p-ctor {n = n} sargs)
      = let (ws , wd , we) = ⇉-diamond-ctor (p-ctor-tail st) (p-ctor sargs)
        in tm-ctor n ws , wd , we
    ⇉-diamond (p-ctor-tail st) (p-ctor-tail st′) =
      let (ws , wd , we) = ⇉-diamond-ctor st st′
      in _ , ⇉*-ctor-tail wd , ⇉*-ctor-tail we
    ⇉-diamond (p-effect_type st) (p-effect_type st′) =
      let (t″ , td , te) = ⇉-diamond st st′
      in _ , ⇉*-effect_type td , ⇉*-effect_type te
    ⇉-diamond (p-effect_pure st) (p-effect_pure st′) =
      let (t″ , td , te) = ⇉-diamond st st′
      in _ , ⇉*-effect_pure td , ⇉*-effect_pure te
    ⇉-diamond (p-effect_bind se sk) (p-effect_bind se′ sk′) =
      let (e″ , ed , ee) = ⇉-diamond se se′
          (k″ , kd , ke) = ⇉-diamond sk sk′
      in _ , ⇉*-trans (⇉*-effect_bind₁ ed) (⇉*-effect_bind₂ kd)
           , ⇉*-trans (⇉*-effect_bind₁ ee) (⇉*-effect_bind₂ ke)
    -- let: reflexivity (p-let) vs ζ.
    ⇉-diamond (p-let sty sv sb) (p-let sty′ sv′ sb′) =
      let (ty″ , tyd , tye) = ⇉-diamond sty sty′
          (v″ , vd , ve) = ⇉-diamond sv sv′
          (b″ , bd , be) = ⇉-diamond sb sb′
      in _ , ⇉*-trans (⇉*-trans (⇉*-let-ty tyd) (⇉*-let-val vd)) (⇉*-let-body bd)
           , ⇉*-trans (⇉*-trans (⇉*-let-ty tye) (⇉*-let-val ve)) (⇉*-let-body be)
    ⇉-diamond (p-ζ sty sv sb) (p-ζ sty′ sv′ sb′) =
      let (v‴ , vd , ve) = ⇉-diamond sv sv′
          (b‴ , bd , be) = ⇉-diamond-star sb sb′
      in substTopT v‴ b‴ , substTopT-⇉* vd bd , substTopT-⇉* ve be
    ⇉-diamond (p-ζ sty sv sb) (p-let sty′ sv′ sb′) =
      let (v‴ , vd , ve) = ⇉-diamond sv sv′
          (b‴ , bd , be) = ⇉-diamond-star sb (⇉*-step sb′ ⇉*-refl)
      in substTopT v‴ b‴
       , substTopT-⇉* vd bd
       , ⇉*-trans (⇉*-step (p-ζ (⇉-refl _) (⇉-refl _) ⇉*-refl) ⇉*-refl)
                  (substTopT-⇉* ve be)
    ⇉-diamond (p-let sty sv sb) (p-ζ sty′ sv′ sb′) =
      let (v‴ , vd , ve) = ⇉-diamond sv sv′
          (b‴ , bd , be) = ⇉-diamond-star (⇉*-step sb ⇉*-refl) sb′
      in substTopT v‴ b‴
       , ⇉*-trans (⇉*-step (p-ζ (⇉-refl _) (⇉-refl _) ⇉*-refl) ⇉*-refl)
                  (substTopT-⇉* vd bd)
       , substTopT-⇉* ve be
    -- β vs app.
    ⇉-diamond (p-β sd sb sa) (p-β sd′ sb′ sa′) =
      let (a‴ , ad , ae) = ⇉-diamond sa sa′
          (b‴ , bd , be) = ⇉-diamond-star sb sb′
      in substTopT a‴ b‴ , substTopT-⇉* ad bd , substTopT-⇉* ae be
    ⇉-diamond (p-β sd sb sa) (p-app (p-lam se sf) sa′) =
      let (a‴ , ad , ae) = ⇉-diamond sa sa′
          (b‴ , bd , be) = ⇉-diamond-star sb (⇉*-step sf ⇉*-refl)
      in substTopT a‴ b‴
       , substTopT-⇉* ad bd
       , ⇉*-trans (⇉*-step (p-β (⇉-refl _) ⇉*-refl (⇉-refl _)) ⇉*-refl)
                  (substTopT-⇉* ae be)
    ⇉-diamond (p-app (p-lam se sf) sa) (p-β sd sb sa′) =
      let (a‴ , ad , ae) = ⇉-diamond sa sa′
          (b‴ , bd , be) = ⇉-diamond-star (⇉*-step sf ⇉*-refl) sb
      in substTopT a‴ b‴
       , ⇉*-trans (⇉*-step (p-β (⇉-refl _) ⇉*-refl (⇉-refl _)) ⇉*-refl)
                  (substTopT-⇉* ad bd)
       , substTopT-⇉* ae be
    ⇉-diamond (p-ι {brs = brs} {c = c} {ar = ar} {b = b} {b′ = b′} {args = args} {args′ = args′} found len sm sbrs sbs sargs)
              (p-ι {brs = .brs} {c = .c} {ar = ar′} {b = b₁} {b′ = b″} {args = .args} {args′ = args″} found′ len′ sm′ sbrs′ sbs′ sargs′) =
      let (args‴ , ad , ae) = ⇉-diamond-terms sargs sargs′
          (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq c ar _ bs-d found
          (b‴′ , found‴′ , b″-⇉) = findBranch-⇉*ᵇ-eq c ar′ _ bs-e found′
          b-eq = proj₂ (findBranch-unique c brs‴ found‴ (subst (λ z → findBranch c brs‴ ≡ just (c , z , b‴′))
                                                              (sym (trans (sym len) len′)) found‴′))
      in substArgs args‴ b‴
       , substArgs-⇉*ᵗ* args′ args‴ ad b′-⇉
       , subst (λ z → _⇉*_ (substArgs args″ b″) (substArgs args‴ z)) (sym b-eq)
               (substArgs-⇉*ᵗ* args″ args‴ ae b″-⇉)
    ⇉-diamond (p-ι-nat-zero {brs = brs} {brs′ = brs′} {ar = ar} {b′ = b′} found refl sm sbrs sbs)
              (p-ι-nat-zero {brs = .brs} {brs′ = brs′₁} {ar = ar′} {b′ = b″} found′ refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "Z" ar _ bs-d found
          (b‴′ , found‴′ , b″-⇉) = findBranch-⇉*ᵇ-eq "Z" ar′ _ bs-e found′
          b-eq = proj₂ (findBranch-unique "Z" brs‴ found‴ found‴′)
      in substArgs [] b‴
       , substArgs-⇉*ᵗ* [] [] ⇉ᵗ*-nil b′-⇉
       , subst (λ z → _⇉*_ (substArgs [] b″) (substArgs [] z)) (sym b-eq)
               (substArgs-⇉*ᵗ* [] [] ⇉ᵗ*-nil b″-⇉)
    ⇉-diamond (p-ι-nat-suc {brs = brs} {brs′ = brs′} {ar = ar} {b′ = b′} {n = n} found refl sm sbrs sbs)
              (p-ι-nat-suc {brs = .brs} {brs′ = brs′₁} {ar = ar′} {b′ = b″} {n = n} found′ refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "S" ar _ bs-d found
          (b‴′ , found‴′ , b″-⇉) = findBranch-⇉*ᵇ-eq "S" ar′ _ bs-e found′
          b-eq = proj₂ (findBranch-unique "S" brs‴ found‴ found‴′)
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl) ⇉ᵗ*-nil
      in substArgs (tm-nat_lit n ∷ []) b‴
       , substArgs-⇉*ᵗ* (tm-nat_lit n ∷ []) (tm-nat_lit n ∷ []) a⇉ b′-⇉
       , subst (λ z → _⇉*_ (substArgs (tm-nat_lit n ∷ []) b″) (substArgs (tm-nat_lit n ∷ []) z))
               (sym b-eq) (substArgs-⇉*ᵗ* (tm-nat_lit n ∷ []) (tm-nat_lit n ∷ []) a⇉ b″-⇉)
    ⇉-diamond (p-ι-bounded-zero {brs = brs} {brs′ = brs′} {ar = ar} {b′ = b′} found refl sm sbrs sbs)
              (p-ι-bounded-zero {brs = .brs} {brs′ = brs′₁} {ar = ar′} {b′ = b″} found′ refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "First" ar _ bs-d found
          (b‴′ , found‴′ , b″-⇉) = findBranch-⇉*ᵇ-eq "First" ar′ _ bs-e found′
          b-eq = proj₂ (findBranch-unique "First" brs‴ found‴ found‴′)
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl) ⇉ᵗ*-nil
      in substArgs (tm-nat_lit 0 ∷ []) b‴
       , substArgs-⇉*ᵗ* (tm-nat_lit 0 ∷ []) (tm-nat_lit 0 ∷ []) a⇉ b′-⇉
       , subst (λ z → _⇉*_ (substArgs (tm-nat_lit 0 ∷ []) b″) (substArgs (tm-nat_lit 0 ∷ []) z))
               (sym b-eq) (substArgs-⇉*ᵗ* (tm-nat_lit 0 ∷ []) (tm-nat_lit 0 ∷ []) a⇉ b″-⇉)
    ⇉-diamond (p-ι-bounded-suc {brs = brs} {brs′ = brs′} {ar = ar} {b′ = b′} {k = k} found refl sm sbrs sbs)
              (p-ι-bounded-suc {brs = .brs} {brs′ = brs′₁} {ar = ar′} {b′ = b″} {k = k} found′ refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "Next" ar _ bs-d found
          (b‴′ , found‴′ , b″-⇉) = findBranch-⇉*ᵇ-eq "Next" ar′ _ bs-e found′
          b-eq = proj₂ (findBranch-unique "Next" brs‴ found‴ found‴′)
          args = tm-nat_lit k ∷ tm-bounded_lit k ∷ []
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl)
                       (⇉ᵗ*-cons (⇉*-step p-bounded_lit ⇉*-refl) ⇉ᵗ*-nil)
      in substArgs args b‴
       , substArgs-⇉*ᵗ* args args a⇉ b′-⇉
       , subst (λ z → _⇉*_ (substArgs args b″) (substArgs args z)) (sym b-eq)
               (substArgs-⇉*ᵗ* args args a⇉ b″-⇉)
    -- ι vs case: the case side reduces the constructor scrutinee. We
    -- delegate to helpers that pattern-match the ctor reduction `ss`.
    ⇉-diamond (p-ι {brs = brs} {c = c} {ar = ar} {b′ = b′} {args = args} {args′ = args′} found len sm sbrs sbs sargs)
              (p-case {s′ = s′} {m′ = m′} {brs′ = brs″} ss sm′ sbs′) =
      ι-vs-case {s′ = s′} found len sbrs sbs sargs ss sm′ sbs′
    ⇉-diamond (p-case {s = s} {s′ = s′} {m = m} {m′ = m′} {brs = brs} {brs′ = red} ss sm sbs)
              (p-ι {m′ = m″} {brs = .brs} {brs′ = brs′} {c = c} {ar = ar} {b = b} {b′ = b′} {args = args} {args′ = args′} found len sm′ sbrs′ sbs′ sargs′) =
      case-vs-ι {m = m} {m′ = m′} {m″ = m″} {src = brs} {red′ = brs′} {c = c} {ar = ar}
                {b = b} {b′ = b′} {args = args} {args′ = args′} {s′ = s′}
                red found len sbs sbrs′ sargs′ ss sm sm′
    -- ι-nat / ι-bounded vs case: the scrutinee is a literal, which only
    -- reduces to itself (`p-nat_lit`), so the case side's scrutinee is fixed.
    ⇉-diamond (p-ι-nat-zero {brs′ = brs′} {ar = ar} {b′ = b′} found refl sm sbrs sbs)
              (p-case {s′ = .(tm-nat_lit 0)} {brs′ = red′} p-nat_lit sm′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "Z" {bs = _} {bs′ = brs‴} ar _ bs-d found
          (m‴ , md , me) = ⇉-diamond sm sm′
      in substArgs [] b‴
       , substArgs-⇉*ᵗ* [] [] ⇉ᵗ*-nil b′-⇉
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-nat_lit ⇉*-refl)) (⇉*-case-motive me))
                  (⇉*-trans (⇉*-case-brs bs-e)
                    (⇉*-step (p-ι-nat-zero {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
    ⇉-diamond (p-case {s = s} {brs = src} p-nat_lit sm sbs)
              (p-ι-nat-zero {ar = ar} {b′ = b′} found refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "Z" {bs = _} {bs′ = brs‴} ar _ bs-e found
          (m‴ , md , me) = ⇉-diamond sm sm′
      in substArgs [] b‴
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-nat_lit ⇉*-refl)) (⇉*-case-motive md))
                  (⇉*-trans (⇉*-case-brs bs-d)
                    (⇉*-step (p-ι-nat-zero {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
       , substArgs-⇉*ᵗ* [] [] ⇉ᵗ*-nil b′-⇉

    ⇉-diamond (p-ι-nat-suc {brs′ = brs′} {ar = ar} {b′ = b′} {n = n} found refl sm sbrs sbs)
              (p-case {s′ = .(tm-nat_lit (suc n))} {brs′ = red′} p-nat_lit sm′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "S" ar _ bs-d found
          (m‴ , md , me) = ⇉-diamond sm sm′
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl) ⇉ᵗ*-nil
      in substArgs (tm-nat_lit n ∷ []) b‴
       , substArgs-⇉*ᵗ* (tm-nat_lit n ∷ []) (tm-nat_lit n ∷ []) a⇉ b′-⇉
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-nat_lit ⇉*-refl)) (⇉*-case-motive me))
                  (⇉*-trans (⇉*-case-brs bs-e)
                    (⇉*-step (p-ι-nat-suc {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
    ⇉-diamond (p-case {s = s} {brs = src} p-nat_lit sm sbs)
              (p-ι-nat-suc {ar = ar} {b′ = b′} {n = n} found refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "S" ar _ bs-e found
          (m‴ , md , me) = ⇉-diamond sm sm′
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl) ⇉ᵗ*-nil
      in substArgs (tm-nat_lit n ∷ []) b‴
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-nat_lit ⇉*-refl)) (⇉*-case-motive md))
                  (⇉*-trans (⇉*-case-brs bs-d)
                    (⇉*-step (p-ι-nat-suc {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
       , substArgs-⇉*ᵗ* (tm-nat_lit n ∷ []) (tm-nat_lit n ∷ []) a⇉ b′-⇉
    ⇉-diamond (p-ι-bounded-zero {brs′ = brs′} {ar = ar} {b′ = b′} found refl sm sbrs sbs)
              (p-case {s′ = .(tm-bounded_lit 0)} {brs′ = red′} p-bounded_lit sm′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "First" ar _ bs-d found
          (m‴ , md , me) = ⇉-diamond sm sm′
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl) ⇉ᵗ*-nil
      in substArgs (tm-nat_lit 0 ∷ []) b‴
       , substArgs-⇉*ᵗ* (tm-nat_lit 0 ∷ []) (tm-nat_lit 0 ∷ []) a⇉ b′-⇉
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-bounded_lit ⇉*-refl)) (⇉*-case-motive me))
                  (⇉*-trans (⇉*-case-brs bs-e)
                    (⇉*-step (p-ι-bounded-zero {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
    ⇉-diamond (p-case {s = s} {brs = src} p-bounded_lit sm sbs)
              (p-ι-bounded-zero {ar = ar} {b′ = b′} found refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "First" ar _ bs-e found
          (m‴ , md , me) = ⇉-diamond sm sm′
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl) ⇉ᵗ*-nil
      in substArgs (tm-nat_lit 0 ∷ []) b‴
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-bounded_lit ⇉*-refl)) (⇉*-case-motive md))
                  (⇉*-trans (⇉*-case-brs bs-d)
                    (⇉*-step (p-ι-bounded-zero {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
       , substArgs-⇉*ᵗ* (tm-nat_lit 0 ∷ []) (tm-nat_lit 0 ∷ []) a⇉ b′-⇉
    ⇉-diamond (p-ι-bounded-suc {brs′ = brs′} {ar = ar} {b′ = b′} {k = k} found refl sm sbrs sbs)
              (p-case {s′ = .(tm-bounded_lit (suc k))} {brs′ = red′} p-bounded_lit sm′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "Next" ar _ bs-d found
          (m‴ , md , me) = ⇉-diamond sm sm′
          args = tm-nat_lit k ∷ tm-bounded_lit k ∷ []
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl)
                       (⇉ᵗ*-cons (⇉*-step p-bounded_lit ⇉*-refl) ⇉ᵗ*-nil)
      in substArgs args b‴
       , substArgs-⇉*ᵗ* args args a⇉ b′-⇉
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-bounded_lit ⇉*-refl)) (⇉*-case-motive me))
                  (⇉*-trans (⇉*-case-brs bs-e)
                    (⇉*-step (p-ι-bounded-suc {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
    ⇉-diamond (p-case {s = s} {brs = src} p-bounded_lit sm sbs)
              (p-ι-bounded-suc {ar = ar} {b′ = b′} {k = k} found refl sm′ sbrs′ sbs′) =
      let (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq "Next" ar _ bs-e found
          (m‴ , md , me) = ⇉-diamond sm sm′
          args = tm-nat_lit k ∷ tm-bounded_lit k ∷ []
          a⇉ = ⇉ᵗ*-cons (⇉*-step p-nat_lit ⇉*-refl)
                       (⇉ᵗ*-cons (⇉*-step p-bounded_lit ⇉*-refl) ⇉ᵗ*-nil)
      in substArgs args b‴
       , ⇉*-trans (⇉*-trans (⇉*-case (⇉*-step p-bounded_lit ⇉*-refl)) (⇉*-case-motive md))
                  (⇉*-trans (⇉*-case-brs bs-d)
                    (⇉*-step (p-ι-bounded-suc {brs = brs‴} {brs′ = brs‴} {ar = _} {b = _} {b′ = b‴}
                                   found‴ refl (⇉-refl _) (⇉-refl-brs _) ⇉*-refl) ⇉*-refl))
       , substArgs-⇉*ᵗ* args args a⇉ b′-⇉

    ⇉-diamond (p-case ss sm sbs) (p-case ss′ sm′ sbs′) =
      let (s″ , sd , se) = ⇉-diamond ss ss′
          (m″ , md , me) = ⇉-diamond sm sm′
          (bs″ , bd , be) = ⇉-diamond-brs sbs sbs′
      in _ , ⇉*-trans (⇉*-trans (⇉*-case sd) (⇉*-case-motive md)) (⇉*-case-brs bd)
           , ⇉*-trans (⇉*-trans (⇉*-case se) (⇉*-case-motive me)) (⇉*-case-brs be)

    -- ι vs case, `p-ι` first: the case side reduces the scrutinee, so its
    -- reduct is `tm-case (tm-ctor c args″) m′ brs′`. We pattern-match the ctor
    -- reduction `ss` to expose `args″`.
    -- ι vs case, `p-ι` first: the `p-ι` reduct is `substArgs args′ b′`; the
    -- case side's reduct is `tm-case s′ m′ red′`. We diamond the two branch
    -- lists and re-apply `p-ι` on the case side.
    ι-vs-case : ∀ {m m′ src red red′ c ar b b′ args args′ s′}
      → findBranch c red ≡ just (c , ar , b′)
      → length args ≡ ar
      → src ⇉*ᵇ red → b ⇉* b′ → args ⇉*ᵗ args′
      → (ss : _⇉_ (tm-ctor c args) s′)
      → m ⇉ m′ → src ⇉*ᵇ red′
      → ∃ λ w → substArgs args′ b′ ⇉* w
               × tm-case s′ m′ red′ ⇉* w
    ι-vs-case {m′ = m′} {red′ = red′} {c = c} {args = args} {args′ = args′} {s′ = s′} found len sbrs sbs sargs ss sm′ sbs′ =
      let (args″ , eq″ , sp) = ⇉-ctor-spine ss
          (args‴ , ad , ae) = ⇉-diamond-terms sp sargs
          (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq c _ _ bs-d found
          len″ : length args″ ≡ _
          len″ = trans (⇉-terms-length sp) len
      in substArgs args‴ b‴
       , substArgs-⇉*ᵗ* args′ args‴ ae b′-⇉
       , subst (λ z → tm-case z m′ red′ ⇉* substArgs args‴ b‴)
               (sym eq″)
               (⇉*-trans (⇉*-case-motive ⇉*-refl)
                  (⇉*-trans (⇉*-case-brs bs-e)
                    (⇉*-trans (⇉*-step (p-ι {brs = brs‴} {brs′ = brs‴} {c = c} {ar = _} {b = _} {b′ = b‴}
                                             {args = args″} {args′ = args″}
                                             found‴ (trans (⇉-terms-length sp) len)
                                             (⇉-refl _) (⇉-refl-brs _) ⇉*-refl (⇉-refl-terms _))
                                        ⇉*-refl)
                              (substArgs-⇉*ᵗ* args″ args‴ ad (⇉*-refl {b‴})))))
    case-vs-ι : ∀ {m m′ m″ src red′ c ar b b′ args args′ s′} (red : List Branch)
      → findBranch c red′ ≡ just (c , ar , b′)
      → length args ≡ ar
      → src ⇉*ᵇ red → src ⇉*ᵇ red′ → args ⇉*ᵗ args′
      → (ss : _⇉_ (tm-ctor c args) s′)
      → m ⇉ m′ → m ⇉ m″
      → ∃ λ w → tm-case s′ m′ red ⇉* w
               × substArgs args′ b′ ⇉* w
    case-vs-ι {m′ = m′} {c = c} {args = args} {args′ = args′} {s′ = s′} red found len sbrs sbrs′ sargs ss sm sm′ =
      let (args″ , eq″ , sp) = ⇉-ctor-spine ss
          (args‴ , ad , ae) = ⇉-diamond-terms sp sargs
          (brs‴ , bs-d , bs-e) = ⇉-diamond-brs sbrs sbrs′
          (b‴ , found‴ , b′-⇉) = findBranch-⇉*ᵇ-eq c _ _ bs-e found
          (m‴ , md , me) = ⇉-diamond sm sm′
          len″ : length args″ ≡ _
          len″ = trans (⇉-terms-length sp) len
      in substArgs args‴ b‴
       , subst (λ z → tm-case z m′ red ⇉* substArgs args‴ b‴)
               (sym eq″)
               (⇉*-trans (⇉*-case-motive md)
                  (⇉*-trans (⇉*-case-brs bs-d)
                    (⇉*-trans (⇉*-step (p-ι {brs = brs‴} {brs′ = brs‴} {c = c} {ar = _} {b = _} {b′ = b‴}
                                             {args = args″} {args′ = args″}
                                             found‴ (trans (⇉-terms-length sp) len)
                                             (⇉-refl _) (⇉-refl-brs _) ⇉*-refl (⇉-refl-terms _))
                                        ⇉*-refl)
                              (substArgs-⇉*ᵗ* args″ args‴ ad (⇉*-refl {b‴})))))
       , substArgs-⇉*ᵗ* args′ args‴ ae b′-⇉

    ⇉-diamond-star : ∀ {t u v} → _⇉*_ t u → _⇉*_ t v → ∃ λ w → _⇉*_ u w × _⇉*_ v w
    ⇉-diamond-star ⇉*-refl q = _ , q , ⇉*-refl
    ⇉-diamond-star p ⇉*-refl = _ , ⇉*-refl , p
    ⇉-diamond-star (⇉*-step s ss) (⇉*-step s′ ss′) =
      let (w , wd , we) = ⇉-diamond s s′
          (w′ , wd′ , we′) = ⇉-diamond-star ss wd
          (w″ , wf , wg) = ⇉-diamond-star ss′ we
          (w‴ , wh , wi) = ⇉-diamond-star we′ wg
      in w‴ , ⇉*-trans wd′ wh , ⇉*-trans wf wi

    ⇉-diamond-terms : ∀ {ts us vs} → _⇉*ᵗ_ ts us → _⇉*ᵗ_ ts vs
                    → ∃ λ ws → _⇉*ᵗ*_ us ws × _⇉*ᵗ*_ vs ws
    ⇉-diamond-terms ⇉*-nil ⇉*-nil = _ , ⇉ᵗ*-nil , ⇉ᵗ*-nil
    ⇉-diamond-terms (⇉*-cons sx sxs) (⇉*-cons sy sys) =
      let (x″ , xd , xe) = ⇉-diamond sx sy
          (xs″ , xsd , xse) = ⇉-diamond-terms sxs sys
      in x″ ∷ xs″ , ⇉ᵗ*-cons xd xsd , ⇉ᵗ*-cons xe xse

    ⇉-diamond-brs : ∀ {bs us vs} → _⇉*ᵇ_ bs us → _⇉*ᵇ_ bs vs
                  → ∃ λ ws → _⇉*ᵇ_ us ws × _⇉*ᵇ_ vs ws
    ⇉-diamond-brs ⇉ᵇ-nil ⇉ᵇ-nil = _ , ⇉ᵇ-nil , ⇉ᵇ-nil
    ⇉-diamond-brs (⇉ᵇ-cons {cn = cn} {ar = ar} sbs sbs′) (⇉ᵇ-cons sbs₁ sbs₂) =
      let (b″ , bd , be) = ⇉-diamond-star sbs sbs₁
          (bs″ , bsd , bse) = ⇉-diamond-brs sbs′ sbs₂
      in (cn , ar , b″) ∷ bs″ , ⇉ᵇ-cons bd bsd , ⇉ᵇ-cons be bse

    ⇉-diamond-ctor : ∀ {n xs ys zs} → _⇉_ (tm-ctor n xs) (tm-ctor n ys)
                   → _⇉_ (tm-ctor n xs) (tm-ctor n zs)
                   → ∃ λ ws → _⇉*_ (tm-ctor n ys) (tm-ctor n ws)
                            × _⇉*_ (tm-ctor n zs) (tm-ctor n ws)
    ⇉-diamond-ctor (p-ctor sxs) (p-ctor sys) =
      let (ws , wd , we) = ⇉-diamond-terms sxs sys
      in ws , ⇉*-ctor* [] _ _ wd , ⇉*-ctor* [] _ _ we
    ⇉-diamond-ctor (p-ctor sxs) (p-ctor-head sx) =
      let (ws , wd , we) = ⇉-diamond-terms sxs (⇉*-cons sx (⇉-refl-terms _))
      in ws , ⇉*-ctor* [] _ _ wd , ⇉*-ctor* [] _ _ we
    ⇉-diamond-ctor (p-ctor-head sx) (p-ctor sxs) =
      let (ws , wd , we) = ⇉-diamond-terms (⇉*-cons sx (⇉-refl-terms _)) sxs
      in ws , ⇉*-ctor* [] _ _ wd , ⇉*-ctor* [] _ _ we
    ⇉-diamond-ctor (p-ctor sxs) (p-ctor-tail {x = x} {xs′ = ys} st) =
      let (ws , wd , we) = ⇉-diamond-terms sxs (⇉*-cons (⇉-refl x) (ctor-spine-rewrite st))
      in ws , ⇉*-ctor* [] _ _ wd , ⇉*-ctor* [] _ _ we
    ⇉-diamond-ctor (p-ctor-tail {x = x} {xs′ = ys} st) (p-ctor sxs) =
      let (ws , wd , we) = ⇉-diamond-terms (⇉*-cons (⇉-refl x) (ctor-spine-rewrite st)) sxs
      in ws , ⇉*-ctor* [] _ _ wd , ⇉*-ctor* [] _ _ we
    ⇉-diamond-ctor (p-ctor-head sx) (p-ctor-head sy) =
      let (x″ , xd , xe) = ⇉-diamond sx sy
      in _ , ⇉*-ctor-head xd , ⇉*-ctor-head xe
    ⇉-diamond-ctor (p-ctor-head sx) (p-ctor-tail st) =
      _ , ⇉*-step (p-ctor-tail st) ⇉*-refl , ⇉*-step (p-ctor-head sx) ⇉*-refl
    ⇉-diamond-ctor (p-ctor-tail st) (p-ctor-head sx) =
      _ , ⇉*-step (p-ctor-head sx) ⇉*-refl , ⇉*-step (p-ctor-tail st) ⇉*-refl
    ⇉-diamond-ctor (p-ctor-tail st) (p-ctor-tail st′) =
      let (ws , wd , we) = ⇉-diamond-ctor st st′
      in _ , ⇉*-ctor-tail wd , ⇉*-ctor-tail we

  ------------------------------------------------------------------------
  -- Confluence of `_⇝_`.
  --
  -- The diamond property of `_⇉_` (multi-step conclusions) plus the two
  -- inclusions `_⇝_ ⊆ _⇉_` (`⇝→⇉`) and `_⇉_ ⊆ _⇝*_` (`⇉→⇝*`) give
  -- confluence of `_⇝_`: `_⇉_` is confluent (its diamond lifts to `_⇉*_`),
  -- and `_⇝_` is sandwiched between `_⇉_` and `_⇉*_`.
  ------------------------------------------------------------------------

  -- `_⇉_` is confluent (its diamond, iterated).
  ⇉-confluent : ∀ {t u v} → _⇉*_ t u → _⇉*_ t v → ∃ λ w → _⇉*_ u w × _⇉*_ v w
  ⇉-confluent = ⇉-diamond-star

  -- `_⇝_` is confluent.
  confluence : ∀ {t u v} → _⇝*_ sig t u → _⇝*_ sig t v
             → ∃ λ w → _⇝*_ sig u w × _⇝*_ sig v w
  confluence {t = t} {u = u} {v = v} tu tv =
    let (w , wu , wv) = ⇉-confluent (⇝→⇉* tu) (⇝→⇉* tv)
    in w , ⇉→⇝*-star wu , ⇉→⇝*-star wv
