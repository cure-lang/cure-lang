------------------------------------------------------------------------
-- `Final`-preservation: the fuel-indexed soundness needs that a final
-- term stays final as it steps.
--
--   final-preservation : Final t → t ⇝ t′ → Final t′
--
-- This is the third input to the constructive soundness theorem, alongside
-- Progress (Proof/Progress.agda) and Preservation
-- (Proof/Preservation.agda). It is what lets the fuel-indexed induction
-- re-apply Progress to the reduct: Progress consumes `Final`, and the
-- reduct of a final term must therefore still be final.
--
-- `Final` is "hole-free and absurd-free" (Proof/Progress.agda). The
-- congruence cases of `_⇝_` are structural. The β/ζ/ι cases substitute a
-- FINAL term (or final fields) into a FINAL body, so they rest on the
-- closure of `Final` under a substitution whose every image is final
-- (`substS-final`, below). The δ case unfolds a global to its body: a
-- `Final` global carries no information about its body, so this case is
-- exactly where the totality certificate's well-formedness half is needed —
-- `Certified sig` supplies `Final body′`.
------------------------------------------------------------------------
module Proof.FinalPreservation where

open import Data.Bool using (Bool; true; false)
open import Data.String.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_; reverse; length; map; updateAt)
open import Data.List using () renaming (lookup to listLookup)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Properties using (unfold-reverse)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Signature using (just-inj)
open import Core.Syntax
open import Core.Reduction
open import Proof.Progress using (Final; FinalTerms; FinalBranches;
                                    Certified;
                                    f-type; f-var; f-pi; f-lam; f-let; f-app;
                                    f-data; f-ctor; f-case; f-global;
                                    f-int_type; f-int_lit; f-nat_lit; f-bounded_lit;
                                    f-float_type; f-float_lit; f-binary_type;
                                    f-atom_type; f-atom_lit;
                                    f-effect_type; f-effect_pure; f-effect_bind;
                                    ft[]; ft∷; fb[]; fb∷)

------------------------------------------------------------------------
-- `Final` is closed under renaming.
--
-- `Final` has a constructor for every term former except the hole and
-- absurd, and `f-var` is unconditional (every variable is final). So a
-- renaming — which only rewrites variable indices — cannot destroy
-- finality. This is needed to lift a final substitution under a binder
-- (`extSub` renames its images by `wk`).
------------------------------------------------------------------------

mutual
  rename-final : ∀ {t} (ρ : Ren) → Final t → Final (rename ρ t)
  rename-final ρ (f-type {l}) = f-type
  rename-final ρ (f-var {k}) = f-var
  rename-final ρ (f-pi fd fc) = f-pi (rename-final ρ fd) (rename-final (ext ρ) fc)
  rename-final ρ (f-lam fd fb) = f-lam (rename-final ρ fd) (rename-final (ext ρ) fb)
  rename-final ρ (f-let fty fv fb) =
    f-let (rename-final ρ fty) (rename-final ρ fv) (rename-final (ext ρ) fb)
  rename-final ρ (f-app ff fa) = f-app (rename-final ρ ff) (rename-final ρ fa)
  rename-final ρ (f-data fps fis) = f-data (renameTerms-final ρ fps) (renameTerms-final ρ fis)
  rename-final ρ (f-ctor fargs) = f-ctor (renameTerms-final ρ fargs)
  rename-final ρ (f-case fs fm fbs) =
    f-case (rename-final ρ fs) (rename-final ρ fm) (renameBranches-final ρ fbs)
  rename-final ρ (f-global {n}) = f-global
  rename-final ρ (f-int_type) = f-int_type
  rename-final ρ (f-int_lit {k}) = f-int_lit
  rename-final ρ (f-nat_lit {k}) = f-nat_lit
  rename-final ρ (f-bounded_lit {k}) = f-bounded_lit
  rename-final ρ (f-float_type) = f-float_type
  rename-final ρ (f-float_lit) = f-float_lit
  rename-final ρ (f-binary_type) = f-binary_type
  rename-final ρ (f-atom_type) = f-atom_type
  rename-final ρ (f-atom_lit {n}) = f-atom_lit
  rename-final ρ (f-effect_type ft) = f-effect_type (rename-final ρ ft)
  rename-final ρ (f-effect_pure ft) = f-effect_pure (rename-final ρ ft)
  rename-final ρ (f-effect_bind fe fk) = f-effect_bind (rename-final ρ fe) (rename-final ρ fk)

  renameTerms-final : ∀ {ts} (ρ : Ren) → FinalTerms ts → FinalTerms (renameTerms ρ ts)
  renameTerms-final ρ ft[] = ft[]
  renameTerms-final ρ (ft∷ fx fxs) = ft∷ (rename-final ρ fx) (renameTerms-final ρ fxs)

  renameBranches-final : ∀ {bs} (ρ : Ren) → FinalBranches bs → FinalBranches (renameBranches ρ bs)
  renameBranches-final ρ fb[] = fb[]
  renameBranches-final ρ (fb∷ {cn = cn} {ar = ar} fb fbs) =
    fb∷ (rename-final (ext^ ar ρ) fb) (renameBranches-final ρ fbs)

------------------------------------------------------------------------
-- A substitution whose every image is final.
------------------------------------------------------------------------

FinalSub : Sub → Set
FinalSub σ = ∀ k → Final (σ k)

-- `extSub σ` is final when `σ` is: index 0 is a variable (`f-var`), and
-- index `suc k` is `rename wk (σ k)`, final by `rename-final`.
extSub-final : ∀ {σ} → FinalSub σ → FinalSub (extSub σ)
extSub-final fs zero = f-var
extSub-final fs (suc k) = rename-final wk (fs k)

extSub^-final : ∀ ar {σ} → FinalSub σ → FinalSub (extSub^ ar σ)
extSub^-final zero fs = fs
extSub^-final (suc ar) fs = extSub-final (extSub^-final ar fs)

------------------------------------------------------------------------
-- `Final` is closed under a final substitution.
--
-- If `t` is final and every term `σ` substitutes in is final, then
-- `substS σ t` is final. The branch case extends the substitution by
-- `extSub^ ar`, which stays final (`extSub^-final`).
------------------------------------------------------------------------

mutual
  substS-final : ∀ {t} (σ : Sub) → FinalSub σ → Final t → Final (substS σ t)
  substS-final σ fs (f-type {l}) = f-type
  substS-final σ fs (f-var {k}) = fs k
  substS-final σ fs (f-pi fd fc) = f-pi (substS-final σ fs fd) (substS-final (extSub σ) (extSub-final fs) fc)
  substS-final σ fs (f-lam fd fb) = f-lam (substS-final σ fs fd) (substS-final (extSub σ) (extSub-final fs) fb)
  substS-final σ fs (f-let fty fv fb) =
    f-let (substS-final σ fs fty) (substS-final σ fs fv) (substS-final (extSub σ) (extSub-final fs) fb)
  substS-final σ fs (f-app ff fa) = f-app (substS-final σ fs ff) (substS-final σ fs fa)
  substS-final σ fs (f-data fps fis) = f-data (substTermsS-final σ fs fps) (substTermsS-final σ fs fis)
  substS-final σ fs (f-ctor fargs) = f-ctor (substTermsS-final σ fs fargs)
  substS-final σ fs (f-case fs′ fm fbs) =
    f-case (substS-final σ fs fs′) (substS-final σ fs fm) (substBranchesS-final σ fs fbs)
  substS-final σ fs (f-global {n}) = f-global
  substS-final σ fs (f-int_type) = f-int_type
  substS-final σ fs (f-int_lit {k}) = f-int_lit
  substS-final σ fs (f-nat_lit {k}) = f-nat_lit
  substS-final σ fs (f-bounded_lit {k}) = f-bounded_lit
  substS-final σ fs (f-float_type) = f-float_type
  substS-final σ fs (f-float_lit) = f-float_lit
  substS-final σ fs (f-binary_type) = f-binary_type
  substS-final σ fs (f-atom_type) = f-atom_type
  substS-final σ fs (f-atom_lit {n}) = f-atom_lit
  substS-final σ fs (f-effect_type ft) = f-effect_type (substS-final σ fs ft)
  substS-final σ fs (f-effect_pure ft) = f-effect_pure (substS-final σ fs ft)
  substS-final σ fs (f-effect_bind fe fk) = f-effect_bind (substS-final σ fs fe) (substS-final σ fs fk)

  substTermsS-final : ∀ {ts} (σ : Sub) → FinalSub σ → FinalTerms ts → FinalTerms (substTermsS σ ts)
  substTermsS-final σ fs ft[] = ft[]
  substTermsS-final σ fs (ft∷ fx fxs) = ft∷ (substS-final σ fs fx) (substTermsS-final σ fs fxs)

  substBranchesS-final : ∀ {bs} (σ : Sub) → FinalSub σ → FinalBranches bs → FinalBranches (substBranchesS σ bs)
  substBranchesS-final σ fs fb[] = fb[]
  substBranchesS-final σ fs (fb∷ {ar = ar} fb fbs) =
    fb∷ (substS-final (extSub^ ar σ) (extSub^-final ar fs) fb) (substBranchesS-final σ fs fbs)

------------------------------------------------------------------------
-- The two substitutions the β/ζ/ι rules use are final.
------------------------------------------------------------------------

-- `topSub a` is final when `a` is: index 0 is `a`, the rest are variables.
topSub-final : ∀ {a} → Final a → FinalSub (topSub a)
topSub-final fa zero = fa
topSub-final fa (suc k) = f-var

------------------------------------------------------------------------
-- `argsSub args` is final when `args` are: the field indices map to `args`
-- (final), the rest to variables. `argsSub` walks its argument onto the
-- indices in order, so the proof walks the `FinalTerms` witness in step.
------------------------------------------------------------------------

argsSub-final : ∀ {args} → FinalTerms args → FinalSub (argsSub args)
argsSub-final {args} ft = go-final 0 args ft
  where
    go-final : ∀ k (ys : List Term) → FinalTerms ys → FinalSub (argsSub-go k ys)
    go-final k [] ft[] i = f-var
    go-final k (y ∷ ys) (ft∷ fy fys) zero = fy
    go-final k (y ∷ ys) (ft∷ fy fys) (suc i) = go-final (suc k) ys fys i

------------------------------------------------------------------------
-- A branch's body is final when the branch list is and the branch is a
-- member. `findBranch` returns a member of the list, so this extracts the
-- branch body's finality from the scrutinee's `FinalBranches` witness.
------------------------------------------------------------------------

finalBranches-member : ∀ {bs} → FinalBranches bs → ∀ {cn ar b}
                     → (cn , ar , b) ∈ bs → Final b
finalBranches-member (fb∷ fb fbs) (here refl) = fb
finalBranches-member (fb∷ fb fbs) (there p) = finalBranches-member fbs p
-- Head and tail of a non-empty `FinalTerms`.
ft-head : ∀ {x xs} → FinalTerms (x ∷ xs) → Final x
ft-head (ft∷ fx fxs) = fx

ft-tail : ∀ {x xs} → FinalTerms (x ∷ xs) → FinalTerms xs
ft-tail (ft∷ fx fxs) = fxs

------------------------------------------------------------------------
-- `Final`-preservation.
------------------------------------------------------------------------

module _ (sig : Signature) (cert : Certified sig) where

  mutual
    final-preservation : ∀ {t t′} → Final t → _⇝_ sig t t′ → Final t′
    -- β: `(λx. b) a ⇝ b[x := a]`; `b` and `a` are final.
    final-preservation (f-app (f-lam fd fb) fa) β =
      substS-final (topSub _) (topSub-final fa) fb
    -- ζ: `let x = v in b ⇝ b[x := v]`; `b` and `v` are final.
    final-preservation (f-let fty fv fb) ζ =
      substS-final (topSub _) (topSub-final fv) fb
    -- ι: `case (ctor c args) of … ⇝ b_c[args]`; `b` and `args` are final.
    final-preservation (f-case (f-ctor {args = args} fargs) fm fbs) (ι {c = c} {ar = ar} {b = b} found len) =
      substS-final (argsSub args) (argsSub-final fargs) (finalBranches-member fbs (findBranch-sound c _ found))
    -- ι on a compact Nat literal: the peeled fields are literals (final).
    final-preservation (f-case (f-nat_lit {k = zero}) fm fbs) (ι-nat-zero {ar = ar} {b = b} found refl) =
      substS-final (argsSub []) (argsSub-final ft[]) (finalBranches-member fbs (findBranch-sound "Z" _ found))
    final-preservation (f-case (f-nat_lit {k = suc k}) fm fbs) (ι-nat-suc {ar = ar} {b = b} found refl) =
      substS-final (argsSub (tm-nat_lit k ∷ [])) (argsSub-final (ft∷ f-nat_lit ft[]))
                   (finalBranches-member fbs (findBranch-sound "S" _ found))
    final-preservation (f-case (f-bounded_lit {k = zero}) fm fbs) (ι-bounded-zero {ar = ar} {b = b} found refl) =
      substS-final (argsSub (tm-nat_lit 0 ∷ [])) (argsSub-final (ft∷ f-nat_lit ft[]))
                   (finalBranches-member fbs (findBranch-sound "First" _ found))
    final-preservation (f-case (f-bounded_lit {k = suc k}) fm fbs) (ι-bounded-suc {ar = ar} {b = b} found refl) =
      substS-final (argsSub (tm-nat_lit k ∷ tm-bounded_lit k ∷ []))
                   (argsSub-final (ft∷ f-nat_lit (ft∷ f-bounded_lit ft[])))
                   (finalBranches-member fbs (findBranch-sound "Next" _ found))
    -- δ: the totality certificate supplies the body's finality.
    final-preservation (f-global {n = f}) (δ {body′ = body′} p) = cert p
    -- Congruences.
    final-preservation (f-app ff fa) (ξ-app₁ step) = f-app (final-preservation ff step) fa
    final-preservation (f-app ff fa) (ξ-app₂ step) = f-app ff (final-preservation fa step)
    final-preservation (f-let fty fv fb) (ξ-let step) = f-let fty (final-preservation fv step) fb
    final-preservation (f-let fty fv fb) (ξ-let-ty step) = f-let (final-preservation fty step) fv fb
    final-preservation (f-let fty fv fb) (ξ-let-body step) = f-let fty fv (final-preservation fb step)
    final-preservation (f-case fs fm fbs) (ξ-case step) = f-case (final-preservation fs step) fm fbs
    final-preservation (f-case fs fm fbs) (ξ-case-motive step) = f-case fs (final-preservation fm step) fbs
    final-preservation (f-case fs fm fbs) (ξ-case-brs steps) = f-case fs fm (final-preservation-brs fbs steps)
    final-preservation (f-pi fd fc) (ξ-pi-dom step) = f-pi (final-preservation fd step) fc
    final-preservation (f-pi fd fc) (ξ-pi-cod step) = f-pi fd (final-preservation fc step)
    final-preservation (f-lam fd fb) (ξ-lam-dom step) = f-lam (final-preservation fd step) fb
    final-preservation (f-lam fd fb) (ξ-lam-body step) = f-lam fd (final-preservation fb step)
    final-preservation (f-data fps fis) (ξ-data-params-at i step) =
      f-data (setAt-final fps i step) fis
    final-preservation (f-data fps fis) (ξ-data-indices-at i step) =
      f-data fps (setAt-final fis i step)
    final-preservation (f-ctor fargs) (ξ-ctor-at i step) =
      f-ctor (setAt-final fargs i step)
    final-preservation (f-effect_type ft) (ξ-effect_type step) = f-effect_type (final-preservation ft step)
    final-preservation (f-effect_pure ft) (ξ-effect_pure step) = f-effect_pure (final-preservation ft step)
    final-preservation (f-effect_bind fe fk) (ξ-effect_bind₁ step) = f-effect_bind (final-preservation fe step) fk
    final-preservation (f-effect_bind fe fk) (ξ-effect_bind₂ step) = f-effect_bind fe (final-preservation fk step)

    -- Updating the element at position `i` with the reduct of a `_⇝_` step
    -- keeps a spine final: the element at `i` is final by `final-preservation`,
    -- every other element is unchanged.
    setAt-final : ∀ {xs} (fxs : FinalTerms xs) (i : Fin (len xs)) {x′}
                → _⇝_ sig (lookupAt xs i) x′
                → FinalTerms (setAt xs i x′)
    setAt-final (ft∷ fx fxs) zero step = ft∷ (final-preservation fx step) fxs
    setAt-final (ft∷ fx fxs) (suc i) step = ft∷ fx (setAt-final fxs i step)

    -- A branch list whose bodies reduce stays final.
    final-preservation-brs : ∀ {bs bs′} → FinalBranches bs → _⇝*ᵇ_ sig bs bs′ → FinalBranches bs′
    final-preservation-brs fb[] ⇝ᵇ-nil = fb[]
    final-preservation-brs (fb∷ fb fbs) (⇝ᵇ-cons steps steps′) =
      fb∷ (final-preservation-star fb steps) (final-preservation-brs fbs steps′)

    final-preservation-star : ∀ {b b′} → Final b → _⇝*_ sig b b′ → Final b′
    final-preservation-star fb ⇝*-refl = fb
    final-preservation-star fb (⇝*-step s ss) = final-preservation-star (final-preservation fb s) ss
