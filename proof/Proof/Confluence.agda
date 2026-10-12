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
-- (`⇉-substS`): parallel reduction is closed under substitution, i.e. if
-- every image of `σ` parallel-reduces to the corresponding image of `σ′` and
-- `t ⇉ t′`, then `substS σ t ⇉ substS σ′ t′`. This is what makes the β case
-- of the diamond go through (both reducts substitute into the joined body).
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

module Conf (sig : Signature) where

  -- The parallel relation and its constructors, at this signature.
  open P.Par sig public

  ------------------------------------------------------------------------
  -- Substitution commutation: `⇉` is closed under substitution.
  --
  -- If every image of `σ` parallel-reduces to the corresponding image of
  -- `σ′`, and `t ⇉ t′`, then `substS σ t ⇉ substS σ′ t′`. This is the crux of
  -- the β case of the diamond (both β-reducts substitute into the joined
  -- body), and it is proved by mutual induction on the `⇉` derivation.
  ------------------------------------------------------------------------

  mutual
    ⇉-substS : ∀ {t t′} (σ σ′ : Sub)
             → (∀ k → Value (σ k) × _⇉_ (σ k) (σ′ k))
             → _⇉_ t t′
             → _⇉_ (substS σ t) (substS σ′ t′)
    ⇉-substS σ σ′ h p-type = p-type
    ⇉-substS σ σ′ h (p-var {k}) = proj₂ (h k)
    ⇉-substS σ σ′ h p-global = p-global
    ⇉-substS σ σ′ h p-int_type = p-int_type
    ⇉-substS σ σ′ h p-int_lit = p-int_lit
    ⇉-substS σ σ′ h p-nat_lit = p-nat_lit
    ⇉-substS σ σ′ h p-bounded_lit = p-bounded_lit
    ⇉-substS σ σ′ h p-float_type = p-float_type
    ⇉-substS σ σ′ h p-float_lit = p-float_lit
    ⇉-substS σ σ′ h p-binary_type = p-binary_type
    ⇉-substS σ σ′ h p-atom_type = p-atom_type
    ⇉-substS σ σ′ h p-atom_lit = p-atom_lit
    ⇉-substS σ σ′ h p-hole = p-hole
    ⇉-substS σ σ′ h p-absurd = p-absurd
    ⇉-substS σ σ′ h (p-pi sd sc) =
      p-pi (⇉-substS σ σ′ h sd) (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sc)
    ⇉-substS σ σ′ h (p-lam sd sb) =
      p-lam (⇉-substS σ σ′ h sd) (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sb)
    ⇉-substS σ σ′ h (p-let sty sv sb) =
      p-let (⇉-substS σ σ′ h sty) (⇉-substS σ σ′ h sv)
            (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sb)
    ⇉-substS σ σ′ h (p-app sf sa) = p-app (⇉-substS σ σ′ h sf) (⇉-substS σ σ′ h sa)
    ⇉-substS σ σ′ h (p-data sps sis) =
      p-data (⇉-substS-terms σ σ′ h sps) (⇉-substS-terms σ σ′ h sis)
    ⇉-substS σ σ′ h (p-ctor sargs) = p-ctor (⇉-substS-terms σ σ′ h sargs)
    ⇉-substS σ σ′ h (p-case {brs = brs} ss sm sbs) =
      p-case (⇉-substS σ σ′ h ss) (⇉-substS σ σ′ h sm)
             (⇉-substBranchesS σ σ′ h sbs)
    ⇉-substS σ σ′ h (p-effect_type st) = p-effect_type (⇉-substS σ σ′ h st)
    ⇉-substS σ σ′ h (p-effect_pure st) = p-effect_pure (⇉-substS σ σ′ h st)
    ⇉-substS σ σ′ h (p-effect_bind se sk) =
      p-effect_bind (⇉-substS σ σ′ h se) (⇉-substS σ σ′ h sk)
    -- β: the result substitutes into the joined body; the substitution
    -- composition law `subst-topSub` re-associates the two substitutions.
    ⇉-substS σ σ′ h (p-β {g} {d} {d′} {b} {b′} {a} {a′} va va′ sd sb sa) =
      subst (λ z → _⇉_ (substS σ (tm-app (tm-lam g d b) a)) z)
            (sym (subst-topSub σ′ a′ b′))
            (p-β (substS-Value σ (λ k → proj₁ (h k)) va) (⇉-Value (substS-Value σ (λ k → proj₁ (h k)) va) (⇉-substS σ σ′ h sa))
                 (⇉-substS σ σ′ h sd)
                 (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sb)
                 (⇉-substS σ σ′ h sa))
    ⇉-substS σ σ′ h (p-ζ {g} {ty} {ty′} {v} {v′} {b} {b′} vv vv′ sty sv sb) =
      subst (λ z → _⇉_ (substS σ (tm-let g ty v b)) z)
            (sym (subst-topSub σ′ v′ b′))
            (p-ζ (substS-Value σ (λ k → proj₁ (h k)) vv)
                 (⇉-Value (substS-Value σ (λ k → proj₁ (h k)) vv) (⇉-substS σ σ′ h sv))
                 (⇉-substS σ σ′ h sty) (⇉-substS σ σ′ h sv)
                 (⇉-substS (extSub σ) (extSub σ′) (⇉-extSub h) sb))

    -- Constructor head/tail: the spine relations commute with substitution.
    ⇉-substS σ σ′ h (p-ctor-head sx) = p-ctor-head (⇉-substS σ σ′ h sx)
    ⇉-substS σ σ′ h (p-ctor-tail st) =
      p-ctor-tail (⇉-substS-ctor-tail σ σ′ h st)
    ⇉-substS σ σ′ h (p-ctor {args = args} sargs) =
      p-ctor (⇉-substS-terms σ σ′ h sargs)

    -- ι: the reduct substitutes the constructor's arguments into the branch
    -- body. Substituting the whole case commutes with the field substitution
    -- (`argsSub`/`substArgs`), so the step is `p-ι` on the substituted parts.
    ⇉-substS σ σ′ h (p-ι {m} {m′} {brs} {c} {ar} {b} {args} {args′} found len sm sargs) =
      subst (λ z → _⇉_ (substS σ (tm-case (tm-ctor c args) m brs)) z)
            (subst-argsSub σ args′ b)
            (p-ι found (subst-len σ′ args′ len) (⇉-substS σ σ′ h sm)
                 (⇉-substS-terms σ σ′ h sargs))

    -- `extSub σ` commutes pointwise.
    ⇉-extSub : ∀ {σ σ′} → (∀ k → Value (σ k) × _⇉_ (σ k) (σ′ k))
             → ∀ k → Value (extSub σ k) × _⇉_ (extSub σ k) (extSub σ′ k)
    ⇉-extSub h zero = neutral n-var , p-var
    ⇉-extSub h (suc k) = ⇉-Value (proj₁ (h k)) (p-rename wk (proj₂ (h k))) , p-rename wk (proj₂ (h k))

    ⇉-extSub^ : ∀ ar {σ σ′} → (∀ k → Value (σ k) × _⇉_ (σ k) (σ′ k))
              → ∀ k → _⇉_ (extSub^ ar σ k) (extSub^ ar σ′ k)
    ⇉-extSub^ zero h = h
    ⇉-extSub^ (suc ar) h = ⇉-extSub (⇉-extSub^ ar h)

    -- Substituting a value under a value-substitution yields a value.
    substS-Value : ∀ {t} (σ : Sub) → (∀ k → Value (σ k)) → Value t → Value (substS σ t)
    substS-Value σ sv (canonical c) = canonical (substS-Canonical σ sv c)
    substS-Value σ sv (neutral n) = neutral (substS-Neutral σ sv n)

    substS-Canonical : ∀ {t} (σ : Sub) → (∀ k → Value (σ k)) → Canonical t → Canonical (substS σ t)
    substS-Canonical σ sv c-type = c-type
    substS-Canonical σ sv c-pi = c-pi
    substS-Canonical σ sv c-lam = c-lam
    substS-Canonical σ sv c-data = c-data
    substS-Canonical σ sv c-ctor = c-ctor
    substS-Canonical σ sv c-int_type = c-int_type
    substS-Canonical σ sv c-int_lit = c-int_lit
    substS-Canonical σ sv c-nat_lit = c-nat_lit
    substS-Canonical σ sv c-bounded_lit = c-bounded_lit
    substS-Canonical σ sv c-float_type = c-float_type
    substS-Canonical σ sv c-float_lit = c-float_lit
    substS-Canonical σ sv c-binary_type = c-binary_type
    substS-Canonical σ sv c-atom_type = c-atom_type
    substS-Canonical σ sv c-atom_lit = c-atom_lit
    substS-Canonical σ sv c-effect_type = c-effect_type
    substS-Canonical σ sv c-effect_pure = c-effect_pure
    substS-Canonical σ sv c-effect_bind = c-effect_bind

    substS-Neutral : ∀ {t} (σ : Sub) → (∀ k → Value (σ k)) → Neutral t → Neutral (substS σ t)
    substS-Neutral σ sv n-var = sv _
    substS-Neutral σ sv n-global = n-global
    substS-Neutral σ sv n-hole = n-hole
    substS-Neutral σ sv (n-app nf) = n-app (substS-Neutral σ sv nf)
    substS-Neutral σ sv (n-case ns) = n-case (substS-Neutral σ sv ns)

    -- Substituting a value (under a substitution whose images are values)
    -- yields a value.
    -- `substS σ` of a value is a value (under a value-substitution).
    ⇉-substS-Value : ∀ {t} (σ : Sub) → (∀ k → Value (σ k)) → Value t → Value (substS σ t)
    ⇉-substS-Value = substS-Value

    -- `⇉` preserves valuehood (needed for the β/ζ side conditions under
    -- substitution).
    ⇉-Value : ∀ {t t′} → Value t → _⇉_ t t′ → Value t′
    ⇉-Value (canonical c) st = canonical (⇉-Canonical c st)
    ⇉-Value (neutral n) st = neutral (⇉-Neutral n st)

    ⇉-Canonical : ∀ {t t′} → Canonical t → _⇉_ t t′ → Canonical t′
    ⇉-Canonical c-type p-type = c-type
    ⇉-Canonical c-pi (p-pi _ _) = c-pi
    ⇉-Canonical c-lam (p-lam _ _) = c-lam
    ⇉-Canonical c-data (p-data _ _) = c-data
    ⇉-Canonical c-ctor (p-ctor _) = c-ctor
    ⇉-Canonical c-ctor (p-ctor-head _) = c-ctor
    ⇉-Canonical c-ctor (p-ctor-tail _) = c-ctor
    ⇉-Canonical c-int_type p-int_type = c-int_type
    ⇉-Canonical c-int_lit p-int_lit = c-int_lit
    ⇉-Canonical c-nat_lit p-nat_lit = c-nat_lit
    ⇉-Canonical c-bounded_lit p-bounded_lit = c-bounded_lit
    ⇉-Canonical c-float_type p-float_type = c-float_type
    ⇉-Canonical c-float_lit p-float_lit = c-float_lit
    ⇉-Canonical c-binary_type p-binary_type = c-binary_type
    ⇉-Canonical c-atom_type p-atom_type = c-atom_type
    ⇉-Canonical c-atom_lit p-atom_lit = c-atom_lit
    ⇉-Canonical c-effect_type (p-effect_type _) = c-effect_type
    ⇉-Canonical c-effect_pure (p-effect_pure _) = c-effect_pure
    ⇉-Canonical c-effect_bind (p-effect_bind _ _) = c-effect_bind

    ⇉-Neutral : ∀ {t t′} → Neutral t → _⇉_ t t′ → Neutral t′
    ⇉-Neutral n-var p-var = n-var
    ⇉-Neutral n-global p-global = n-global
    ⇉-Neutral n-hole p-hole = n-hole
    ⇉-Neutral (n-app nf) (p-app sf sa) = n-app (⇉-Neutral nf sf)
    ⇉-Neutral (n-case ns) (p-case ss sm sbs) = n-case (⇉-Neutral ns ss)

    -- Substitution commutes with multi-step parallel reduction.
    ⇉-substS-star : ∀ {t t′} (σ σ′ : Sub) → (∀ k → Value (σ k) × _⇉_ (σ k) (σ′ k))
                  → _⇉*_ t t′ → _⇉*_ (substS σ t) (substS σ′ t′)
    ⇉-substS-star σ σ′ h ⇉*-refl = ⇉*-refl
    ⇉-substS-star σ σ′ h (⇉*-step s ss) =
      ⇉*-step (⇉-substS σ σ′ h s) (⇉-substS-star σ σ′ h ss)

    -- `⇉` commutes with renaming.
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
    p-rename ρ (p-case ss sm) = p-case (p-rename ρ ss) (p-rename ρ sm)
    p-rename ρ (p-effect_type st) = p-effect_type (p-rename ρ st)
    p-rename ρ (p-effect_pure st) = p-effect_pure (p-rename ρ st)
    p-rename ρ (p-effect_bind se sk) = p-effect_bind (p-rename ρ se) (p-rename ρ sk)

    p-rename-terms : ∀ (ρ : Ren) {ts ts′} → _⇉*ᵗ_ ts ts′
                   → _⇉*ᵗ_ (renameTerms ρ ts) (renameTerms ρ ts′)
    p-rename-terms ρ ⇉*-nil = ⇉*-nil
    p-rename-terms ρ (⇉*-cons sx sxs) = ⇉*-cons (p-rename ρ sx) (p-rename-terms ρ sxs)

    ⇉-substS-terms : ∀ {ts ts′} (σ σ′ : Sub) → (∀ k → Value (σ k) × _⇉_ (σ k) (σ′ k))
                   → _⇉*ᵗ_ ts ts′ → _⇉*ᵗ_ (substTermsS σ ts) (substTermsS σ′ ts′)
    ⇉-substS-terms σ σ′ h ⇉*-nil = ⇉*-nil
    ⇉-substS-terms σ σ′ h (⇉*-cons sx sxs) =
      ⇉*-cons (⇉-substS σ σ′ h sx) (⇉-substS-terms σ σ′ h sxs)

    -- Substituting a branch list under pointwise-`⇉` substitutions: each
    -- branch body is substituted under the `ar`-fold extended substitution.
    ⇉-substBranchesS : ∀ {bs bs′} (σ σ′ : Sub) → (∀ k → Value (σ k) × _⇉_ (σ k) (σ′ k))
                     → _⇉*ᵇ_ bs bs′
                     → _⇉*ᵇ_ (substBranchesS σ bs) (substBranchesS σ′ bs′)
    ⇉-substBranchesS σ σ′ h ⇉ᵇ-nil = ⇉ᵇ-nil
    ⇉-substBranchesS σ σ′ h (⇉ᵇ-cons {ar = ar} sbs sbs′) =
      ⇉ᵇ-cons (⇉-substS-star (extSub^ ar σ) (extSub^ ar σ′) (⇉-extSub^ ar h) sbs)
              (⇉-substBranchesS σ σ′ h sbs′)

