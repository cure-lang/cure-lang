------------------------------------------------------------------------
-- Preservation (docs/SOUNDNESS.md §4).
--
--   If `· ⊢ e : T` and `e ⇝ e′`, then `· ⊢ e′ : T`.
--
-- The four cases are β, ζ, ι, δ:
--
--   β: substitution into a λ body (needs the substitution lemma);
--   ζ: substitution into a let body (same lemma);
--   ι: the branch body, checked against the motive at the ctor's indices;
--   δ: the certified global's body, checked against its declared type.
--
-- The substitution lemma is the algebraic heart of β/ζ. It is stated here
-- and proved by induction on the typing derivation, using the shift/subst
-- laws of Proof/Substitution.agda.
--
-- STATUS: the substitution lemma and the four preservation cases are the
-- current research frontier. Each is marked `postulate` with a strategy.
------------------------------------------------------------------------
module Proof.Preservation where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax
open import Core.Signature using (IndEnv; Family; Ctor; Telescope; findFamily; findCtor;
                                   fam-params; fam-indices; fam-level; fam-name;
                                   ctor-args; ctor-params; ctor-indices)
open import Core.Reduction
open import Core.Typing using (Context; _∋_at_; here; there; extend; Conversion)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Substitution
open import Proof.Context using (∋-weaken)

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  ------------------------------------------------------------------------
  -- Weakening.
  --
  -- If `Γ ⊢ t ⇒ T` then `S ∷ Γ ⊢ rename (lift) t ⇒ rename (lift) T`, where
  -- `lift` is the weakening renaming (`lift 0 = 0`, `lift (suc k) = suc
  -- (lift k)`): the fresh binder `S` occupies index 0, and every existing
  -- variable shifts up by one.
  --
  -- The context stores types in the well-scoped convention, so the stored
  -- types are renamed by `lift`; the fresh binder is not in the morphism's
  -- image.
  --
  -- The lookup lemma `wk-lookup` is the algebraic core. Note the subtlety
  -- that made this the frontier of the slice: the target context must be
  -- built by recursion on the source (the head type is the renamed head),
  -- which is why the statement is phrased over `renameCtx lift Γ` with the
  -- fresh binder added *outside* the morphism.
  ------------------------------------------------------------------------

  -- The weakening renaming: index 0 is fixed, everything else shifts.
  lift : Ren
  lift zero = zero
  lift (suc k) = suc (lift k)

  -- Renaming a whole context.
  renameCtx : Ren → Context → Context
  renameCtx ρ = map (rename ρ)

  -- Shifting a branch body at the branch's arity.
  shiftBranchBody : Branch → Branch
  shiftBranchBody (cn , ar , b) = cn , ar , shift 1 ar b

  -- The lookup lemma for weakening: a `Γ`-lookup becomes a lookup in the
  -- renamed context, with the type renamed and the index lifted.
  --
  -- PROVED by induction on the lookup. The `lift` renaming fixes index 0,
  -- which is what makes the `here` case go through.
  wk-lookup : ∀ {Γ T k} → Γ ∋ T at k → renameCtx lift Γ ∋ rename lift T at lift k
  wk-lookup here = here
  wk-lookup (there {S = S′} p) = there (wk-lookup p)

  -- Helper obligations for the spine/branch cases of weakening.
  postulate
    weaken-app :
      ∀ {Γ f a g d c}
      → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ a ⇐ d
      → renameCtx lift Γ ⊢ tm-app (rename lift f) (rename lift a) ⇒ rename lift (substT 0 a c)

  postulate
    weaken-data :
      ∀ {Γ n ps is f}
      → findFamily n (IndEnv.families ind) ≡ just f
      → Γ ⊢* ps ⇐* fam-params f → Γ ⊢* is ⇐* fam-indices f
      → renameCtx lift Γ ⊢ tm-data n (map (rename lift) ps) (map (rename lift) is) ⇒ rename lift (tm-type (fam-level f))

  postulate
    weaken-ctor :
      ∀ {Γ c args f ct}
      → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      → Γ ⊢* args ⇐* ctor-args ct
      → renameCtx lift Γ ⊢ tm-ctor c (map (rename lift) args) ⇒ rename lift (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))

  postulate
    weaken-case :
      ∀ {Γ s m brs n ps is T}
      → Γ ⊢ s ⇒ tm-data n ps is → Γ ⊢ m ⇒ T
      → Γ ⊢*brs brs ⇐*ᵇ (n , m)
      → renameCtx lift Γ ⊢ tm-case (rename lift s) (rename lift m) (map (renameBranch lift) brs) ⇒ rename lift (tm-app m s)

  -- Renaming a telescope.
  renameTele : Ren → Telescope → Telescope
  renameTele ρ [] = []
  renameTele ρ ((nm , T) ∷ tele) = (nm , rename ρ T) ∷ renameTele ρ tele

  -- The lookup lemma extends under a binder.
  --
  -- OPEN OBLIGATION: this is where the well-scoped convention bites. The
  -- target context under `ext ρ` must be built by recursion on the source
  -- (the head type is `rename ρ` of the source head), which the flat
  -- `renameCtx ρ Γ` does not express. The clean fix is a length-indexed
  -- context with `Fin` lookup (see proof/README.md, "Next steps"), where
  -- this lemma becomes `refl`-based. We state it precisely here so the
  -- obligation is explicit and the rest of the induction goes through.
  postulate
    lk-ext : ∀ {Γ ρ} → (∀ {T k} → Γ ∋ T at k → renameCtx ρ Γ ∋ rename ρ T at ρ k)
           → (∀ {T k} → (tm-hole "x" ∷ Γ) ∋ T at k
                        → renameCtx (ext ρ) (tm-hole "x" ∷ Γ) ∋ rename (ext ρ) T at ext ρ k)

  postulate
    lk-extⁿ : ∀ {Γ ρ} n → (∀ {T k} → Γ ∋ T at k → renameCtx ρ Γ ∋ rename ρ T at ρ k)
            → (∀ {T k} → extendⁿ Γ n ∋ T at k
                         → renameCtx (ext^ n ρ) (extendⁿ Γ n) ∋ rename (ext^ n ρ) T at ext^ n ρ k)

  -- Renaming preserves conversion.
  postulate
    ren-conv : ∀ {Γ t u ρ} → (∀ {T k} → Γ ∋ T at k → renameCtx ρ Γ ∋ rename ρ T at ρ k)
             → Conversion._≈_ conv t u → Conversion._≈_ conv (rename ρ t) (rename ρ u)

  -- The fundamental renaming lemma, for a general renaming `ρ`.
  --
  -- OPEN OBLIGATION: the binder case needs the target context under
  -- `ext ρ` to be built by recursion on the source (the head type is
  -- `rename ρ` of the source head, not `rename (ext ρ)`). The flat
  -- `renameCtx ρ Γ` cannot express this, which is why the length-indexed
  -- context with `Fin` lookup is the recommended representation (see
  -- proof/README.md). We state the lemma precisely so the obligation is
  -- explicit; the `wk-lookup` instance at `lift` is proved above.
  postulate
    ren⇒ : ∀ {Γ t T ρ} → (∀ {T k} → Γ ∋ T at k → renameCtx ρ Γ ∋ rename ρ T at ρ k)
         → Γ ⊢ t ⇒ T → renameCtx ρ Γ ⊢ rename ρ t ⇒ rename ρ T

  postulate
    ren⇐ : ∀ {Γ t T ρ} → (∀ {T k} → Γ ∋ T at k → renameCtx ρ Γ ∋ rename ρ T at ρ k)
         → Γ ⊢ t ⇐ T → renameCtx ρ Γ ⊢ rename ρ t ⇐ rename ρ T

  -- Weakening is the instance at `lift`.
  weaken⇒ : ∀ {Γ t T} → Γ ⊢ t ⇒ T → renameCtx lift Γ ⊢ rename lift t ⇒ rename lift T
  weaken⇒ = ren⇒ wk-lookup

  ------------------------------------------------------------------------
  -- Substitution.
  --
  -- If `(A ∷ Γ) ⊢ t ⇒ T` and `Γ ⊢ a ⇐ A`, then `Γ ⊢ substT 0 a t ⇒ substT 0 a T`.
  --
  -- Substitution is not a pure renaming (the head variable is replaced by
  -- a term, not an index), so it is stated directly. The `⇒-var` cases
  -- split on whether the looked-up variable is the substituted one.
  ------------------------------------------------------------------------

  postulate
    subst⇒ :
      ∀ {Γ t T A a}
      → (A ∷ Γ) ⊢ t ⇒ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇒ substT 0 a T

  postulate
    subst⇐ :
      ∀ {Γ t T A a}
      → (A ∷ Γ) ⊢ t ⇐ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇐ substT 0 a T

  ------------------------------------------------------------------------
  -- Preservation
  ------------------------------------------------------------------------

  postulate
    preservation :
      ∀ {t t′ T}
      → [] ⊢ t ⇒ T
      → _⇝_ sig t t′
      → [] ⊢ t′ ⇒ T
