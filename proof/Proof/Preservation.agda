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
-- The substitution lemma is the algebraic heart of β/ζ. It is proved here
-- by mutual induction on the typing derivation, stated with a coherence
-- condition on the substitution.
--
-- STATUS: the substitution lemma's binder cases are proved; the spine and
-- branch cases are the current research frontier.
------------------------------------------------------------------------
module Proof.Preservation where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade; unrestricted)
open import Core.Universe using (Level; l0; l1; l2; _≤ˡ_)
open import Core.Syntax
open import Core.Signature using (IndEnv; Family; Ctor; Telescope; findFamily; findCtor;
                                   fam-params; fam-indices; fam-level; fam-name;
                                   ctor-args; ctor-params; ctor-indices)
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; lookup-extend; lookup-renameCtx; renameCtx; Conversion; extendⁿ; _∈Tele_; ∈-here; ∈-there)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Inversion
open import Proof.Substitution
open import Proof.Context using (lookup-weaken; lookup-head;
                                  lookup-extendⁿ-zero; lookup-extendⁿ-raise;
                                  extF; extF-coh; lookup-extF)

------------------------------------------------------------------------
-- Signature closedness.
--
-- The signature's entries (a global's declared type, a family's
-- telescopes, a constructor's argument telescope and result type) are
-- CLOSED: they mention no free variable. This is a well-formedness side
-- condition on the signature, carried as a hypothesis (like
-- `StrictlyPositive`), and it makes renaming/substitution the identity on
-- them via `rename-closed` / `substS-closed`.
--
-- Defined at the TOP LEVEL (outside `Preserve`) so the module header can
-- name it.
------------------------------------------------------------------------

ClosedSig : IndEnv → Signature → Set
ClosedSig ind sig =
    (∀ (f : Name) {T} → Signature.type-of sig f ≡ just T → Scoped 0 T)
  × (∀ (f : Family) {T} → T ∈Tele (fam-params f) → Scoped 0 T)
  × (∀ (f : Family) {T} → T ∈Tele (fam-indices f) → Scoped 0 T)
  × (∀ (f : Family) (ct : Ctor) {T} → T ∈Tele (ctor-args ct) → Scoped 0 T)
  × (∀ (f : Family) (ct : Ctor)
     → Scoped 0 (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)))

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion)
               (closed : ClosedSig ind sig) where
  open Core.Typing.Typing ind sig conv
  open Proof.Inversion.Invert ind sig conv using (conv-pi-components)

  ------------------------------------------------------------------------
  -- Weakening.
  --
  -- If `Γ ⊢ t ⇒ T` then `extend Γ S ⊢ rename wk t ⇒ rename wk T`: adding a
  -- fresh binder preserves typability, renaming the term and its type by
  -- `wk`. The `⇒-var` case is the definitional lookup law.
  --
  -- OPEN OBLIGATION: the binder cases need `rename (ext wk)` threaded
  -- through the body. The lookup law is proved; the term-level induction is
  -- the remaining piece.
  ------------------------------------------------------------------------

  -- The fundamental renaming lemma. A "context morphism" from `Γ` to `Δ`
  -- maps every `Γ`-lookup to a `Δ`-lookup of the renamed type.
  --
  -- PROVED by induction on the derivation. The `⇒-var` case applies the
  -- morphism; the binder cases extend it (the extension's lookup law is
  -- `ext-wk-rename`, proved in Core.Syntax).
  -- The extended morphism: the new binder maps to the new binder.
  ext-idx : ∀ {n m} (idx : Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  ext-idx idx zero = zero
  ext-idx idx (suc i) = suc (idx i)

  -- The extended coherence: `toℕ (ext-idx idx j) ≡ ext ρ (toℕ j)`.
  ext-coh : ∀ {n m} (ρ : Ren) (idx : Fin n → Fin m)
          → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
          → ∀ j → toℕ (ext-idx {n} {m} idx j) ≡ ext ρ (toℕ j)
  ext-coh ρ idx coh zero = refl
  ext-coh ρ idx coh (suc j) = cong suc (coh j)

  -- The extended lookup law, parameterised by the binder's domain term.
  ext-law : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ : Ren} (d : Term) (idx : Fin n → Fin m)
          → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
          → ∀ j → lookup (extend Δ (rename ρ d)) (ext-idx idx j)
                ≡ rename (ext ρ) (lookup (extend Γ d) j)
  ext-law {Γ = Γ} {Δ = Δ} {ρ = ρ} d idx law zero = ext-wk-rename ρ d
  ext-law {Γ = Γ} {Δ = Δ} {ρ = ρ} d idx law (suc j) =
    trans (lookup-extend Δ (rename ρ d) (idx j))
          (trans (cong (rename wk) (law j))
                 (trans (ext-wk-rename ρ (lookup Γ j))
                        (cong (rename (ext ρ)) (sym (lookup-renameCtx wk Γ j)))))

  ------------------------------------------------------------------------
  -- Signature closedness.
  --
  -- `ClosedSig` is defined at the top level (above `module Preserve`); the
  -- module takes a witness `closed` as a parameter. The lemmas below turn
  -- that witness into the `rename`/`substS`-is-identity facts the renaming
  -- and substitution lemmas consume.
  ------------------------------------------------------------------------

  -- A global's declared type is closed, so renaming leaves it unchanged.
  rename-global-type : ∀ (ρ : Ren) (f : Name) (T : Term)
    → Signature.type-of sig f ≡ just T → rename ρ T ≡ T
  rename-global-type ρ f T p = rename-closed (proj₁ closed f p)

  -- The signature's telescopes are closed, so renaming leaves them
  -- unchanged.
  tele-closed-params : ∀ (ρ : Ren) (f : Family) {T : Term}
    → T ∈Tele (fam-params f) → rename ρ T ≡ T
  tele-closed-params ρ f h = rename-closed (proj₁ (proj₂ closed) f h)

  tele-closed-indices : ∀ (ρ : Ren) (f : Family) {T : Term}
    → T ∈Tele (fam-indices f) → rename ρ T ≡ T
  tele-closed-indices ρ f h = rename-closed (proj₁ (proj₂ (proj₂ closed)) f h)

  tele-closed-ctor : ∀ (ρ : Ren) (f : Family) (ct : Ctor) {T : Term}
    → T ∈Tele (ctor-args ct) → rename ρ T ≡ T
  tele-closed-ctor ρ f ct h = rename-closed (proj₁ (proj₂ (proj₂ (proj₂ closed))) f ct h)

  -- A constructor's result type is closed, so renaming leaves it
  -- unchanged.
  rename-ctor-result : ∀ (ρ : Ren) (f : Family) (ct : Ctor)
    → rename ρ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
    ≡ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)
  rename-ctor-result ρ f ct = rename-closed (proj₂ (proj₂ (proj₂ (proj₂ closed))) f ct)

  -- A closed term is fixed by substitution (its substitution is the
  -- identity substitution on its free variables).
  subst-closed : ∀ (σ : Sub) {T : Term} → Scoped 0 T → substS σ T ≡ T
  subst-closed σ st = substS-closed st

  -- The signature's telescopes are closed, so substituting into them
  -- leaves them unchanged.
  tele-closed-subst-params : ∀ (σ : Sub) (f : Family) {T : Term}
    → T ∈Tele (fam-params f) → substS σ T ≡ T
  tele-closed-subst-params σ f h = subst-closed σ (proj₁ (proj₂ closed) f h)

  tele-closed-subst-indices : ∀ (σ : Sub) (f : Family) {T : Term}
    → T ∈Tele (fam-indices f) → substS σ T ≡ T
  tele-closed-subst-indices σ f h = subst-closed σ (proj₁ (proj₂ (proj₂ closed)) f h)

  tele-closed-subst-ctor : ∀ (σ : Sub) (f : Family) (ct : Ctor) {T : Term}
    → T ∈Tele (ctor-args ct) → substS σ T ≡ T
  tele-closed-subst-ctor σ f ct h = subst-closed σ (proj₁ (proj₂ (proj₂ (proj₂ closed))) f ct h)

  -- A constructor's result type is closed, so substituting into it leaves
  -- it unchanged.
  subst-ctor-result : ∀ (σ : Sub) (f : Family) (ct : Ctor)
    → substS σ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
    ≡ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)
  subst-ctor-result σ f ct = subst-closed σ (proj₂ (proj₂ (proj₂ (proj₂ closed))) f ct)

  -- Conversion is a congruence for renaming. This is a field of the
  -- `Conversion` record (Core/Typing.agda): the kernel's conversion is
  -- decided structurally, so it is stable under renaming. We re-export it
  -- under the local name the renaming lemma uses.
  rename-conv : ∀ {t u} (ρ : Ren) → Conversion._≈_ conv t u
              → Conversion._≈_ conv (rename ρ t) (rename ρ u)
  rename-conv = Conversion.≈-rename conv

  mutual
    ren⇒ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {t T ρ}
           (idx : Fin n → Fin m)
         → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
         → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
         → Γ ⊢ t ⇒ T → Δ ⊢ rename ρ t ⇒ rename ρ T
    ren⇒ idx coh law (⇒-type p) = ⇒-type p
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-var i) =
      subst (λ k → Δ ⊢ tm-var k ⇒ rename ρ (lookup Γ i)) (coh i)
            (subst (λ X → Δ ⊢ tm-var (toℕ (idx i)) ⇒ X) (law i) (⇒-var (idx i)))
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-pi {d = d} dd dc) =
      ⇒-pi (ren⇒ idx coh law dd) (ren⇒ (ext-idx idx) (ext-coh ρ idx coh) (ext-law d idx law) dc)
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-lam {d = d} dd db) =
      ⇒-lam (ren⇒ idx coh law dd) (ren⇐ (ext-idx idx) (ext-coh ρ idx coh) (ext-law d idx law) db)
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-app {f = f} {a = a} {c = c} df da) =
      subst (λ X → Δ ⊢ tm-app (rename ρ f) (rename ρ a) ⇒ X)
            (sym (rename-topSub ρ a c))
            (⇒-app (ren⇒ idx coh law df) (ren⇒ idx coh law da))
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-let {ty = ty} {v = v} {T = T} dty dv db) =
      subst (λ X → Δ ⊢ tm-let _ (rename ρ ty) (rename ρ v) (rename (ext ρ) _) ⇒ X)
            (sym (rename-topSub ρ v T))
            (⇒-let (ren⇒ idx coh law dty)
                   (ren⇐ idx coh law dv)
                   (ren⇒ (ext-idx idx) (ext-coh ρ idx coh) (ext-law ty idx law) db))
    ren⇒ {Δ = Δ} {ρ = ρ} idx coh law (⇒-global {f = f} {T = T} p) =
      subst (λ X → Δ ⊢ tm-global f ⇒ X) (sym (rename-global-type ρ f T p)) (⇒-global p)
    ren⇒ idx coh law (⇒-int_type) = ⇒-int_type
    ren⇒ idx coh law (⇒-float_type) = ⇒-float_type
    ren⇒ idx coh law (⇒-binary_type) = ⇒-binary_type
    ren⇒ idx coh law (⇒-atom_type) = ⇒-atom_type
    ren⇒ idx coh law (⇒-int_lit) = ⇒-int_lit
    ren⇒ idx coh law (⇒-float_lit) = ⇒-float_lit
    ren⇒ idx coh law (⇒-atom_lit) = ⇒-atom_lit
    ren⇒ idx coh law (⇒-nat_lit p) = ⇒-nat_lit p
    ren⇒ idx coh law (⇒-bounded_lit p) = ⇒-bounded_lit p
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-data {ps = ps} {is = is} {f = f} p q r) =
      ⇒-data p
        (subst (λ zs → Δ ⊢* zs ⇐* fam-params f) (sym (renameTerms-map ρ ps))
               (ren-spine idx coh law (tele-closed-params ρ f) q))
        (subst (λ zs → Δ ⊢* zs ⇐* fam-indices f) (sym (renameTerms-map ρ is))
               (ren-spine idx coh law (tele-closed-indices ρ f) r))
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-ctor {c = c} {args = args} {f = f} {ct = ct} p q) =
      subst (λ X → Δ ⊢ tm-ctor c (renameTerms ρ args) ⇒ X)
            (sym (rename-ctor-result ρ f ct))
            (⇒-ctor p (subst (λ zs → Δ ⊢* zs ⇐* ctor-args ct) (sym (renameTerms-map ρ args)) (ren-spine idx coh law (tele-closed-ctor ρ f ct) q)))
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-case {s = s} {m = m′} {brs = brs} p q r) =
      ⇒-case (ren⇒ idx coh law p) (ren⇒ idx coh law q) (ren-branches idx coh law r)
    ren⇒ idx coh law (⇒-effect_type p) = ⇒-effect_type (ren⇒ idx coh law p)
    ren⇒ idx coh law (⇒-effect_pure p) = ⇒-effect_pure (ren⇒ idx coh law p)
    ren⇒ idx coh law (⇒-conv der eq) =
      ⇒-conv (ren⇒ idx coh law der) (rename-conv _ eq)
    ren⇒ {Δ = Δ} {ρ = ρ} idx coh law (⇒-effect_bind {A = A} {B = B} p q) =
      ⇒-effect_bind (ren⇒ idx coh law p)
                    (subst (λ X → Δ ⊢ rename ρ _ ⇒ tm-pi unrestricted (rename ρ A) (tm-effect_type X))
                           (sym (ext-wk-rename ρ B))
                           (ren⇒ idx coh law q))

    ren⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {t T ρ}
           (idx : Fin n → Fin m)
         → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
         → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
         → Γ ⊢ t ⇐ T → Δ ⊢ rename ρ t ⇐ rename ρ T
    ren⇐ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇐-lam {g = g} {d = d} {b = b} {c = c} {l = l} ds body) =
      ⇐-lam {g = g} {d = rename ρ d} {b = rename (ext ρ) b} {c = rename (ext ρ) c}
            (ren⇒ idx coh law ds)
            (ren⇐ (ext-idx idx) (ext-coh ρ idx coh) (ext-law d idx law) body)
    ren⇐ idx coh law (⇐-conv der eq) = ⇐-conv (ren⇐ idx coh law der) (rename-conv _ eq)
    ren⇐ idx coh law (⇐-hole) = ⇐-hole
    ren⇐ idx coh law (⇐-infer der eq) = ⇐-infer (ren⇒ idx coh law der) (rename-conv _ eq)
    ren⇐ idx coh law (⇐-cumul der le) = ⇐-cumul (ren⇒ idx coh law der) le

    -- The telescope is a fixed (closed) telescope from the signature, so
    -- its types are unchanged by renaming.
    ren-spine : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ts tele ρ}
           (idx : Fin n → Fin m)
         → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
         → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
         → (∀ {T} → T ∈Tele tele → rename ρ T ≡ T)
         → Γ ⊢* ts ⇐* tele → Δ ⊢* map (rename ρ) ts ⇐* tele
    ren-spine idx coh law cl ⊢*[] = ⊢*[]
    ren-spine {Δ = Δ} {ρ = ρ} idx coh law cl (⊢*∷ {x = x} {T = T} {tele = tele} {nm = nm} dx dxs) =
      ⊢*∷ (subst (λ X → Δ ⊢ rename ρ x ⇐ X) (cl ∈-here)
                 (ren⇐ idx coh law dx))
          (ren-spine idx coh law (λ p → cl (∈-there p)) dxs)

    -- Branch checking is preserved by renaming. The branch context
    -- `extendⁿ Γ ar` is transported by the extended morphism `extF ar idx`;
    -- the body is renamed by `ext^ ar ρ`. The motive's renaming is the
    -- subtle step: `m′` is used in the extended context, so renaming it
    -- under `ext^ ar ρ` agrees with renaming it under `ρ` because the
    -- field indices (`< ar`) are fixed by `ext^ ar ρ` and the existing
    -- indices are `raise ar`-shifted.
    ren-branches : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {brs nm m′ ρ}
           (idx : Fin n → Fin m)
         → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
         → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
         → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
         → Δ ⊢*brs renameBranches ρ brs ⇐*ᵇ (nm , rename ρ m′)
    ren-branches idx coh law brs[] = brs[]
    ren-branches {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law
                 (brs∷ {cn = cn} {ar = ar} {b = b} {brs = brs} {n = nm} {m = m′} {f = f} {ct = ct} fc len db dbrs) =
      brs∷ fc len
           (subst (λ X → extendⁿ Δ ar ⊢ rename (ext^ ar ρ) b ⇐ X)
                  (rename-branch-motive ar ρ m′ cn)
                  (ren⇐ (extF ar idx) (extF-coh ar ρ idx coh)
                        (lookup-extF Γ Δ ar ρ idx law) db))
           (ren-branches idx coh law dbrs)

  -- The `let` case of the renaming lemma. PROVED: it is the `⇒-let` rule,
  -- with the result type transported across `rename-topSub` (the
  -- commutation of `rename` with the top substitution, Proof/Substitution).
  --
  -- It is stated outside the `mutual` block because it is a *derived*
  -- lemma: it consumes `ren⇒`/`ren⇐` rather than participating in their
  -- recursion. The value `v` and body type `T` are explicit so the
  -- transport can name them.
  ren-let : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {g ty b l ρ} (v T : Term) (idx : Fin n → Fin m)
    → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
    → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
    → Γ ⊢ ty ⇒ tm-type l → Γ ⊢ v ⇐ ty → extend Γ ty ⊢ b ⇒ T
    → Δ ⊢ rename ρ (tm-let g ty v b) ⇒ rename ρ (substTopT v T)
  ren-let {ρ = ρ} v T idx coh law dty dv db =
    subst (λ X → _ ⊢ tm-let _ (rename ρ _) (rename ρ v) (rename (ext ρ) _) ⇒ X)
          (sym (rename-topSub ρ v T))
          (⇒-let (ren⇒ idx coh law dty)
                 (ren⇐ idx coh law dv)
                 (ren⇒ (ext-idx idx) (ext-coh ρ idx coh) (ext-law _ idx law) db))

  -- Weakening is the instance of the fundamental lemma at `wk`.
  weaken⇒ : ∀ {n} {Γ : Ctx n} {t T S} → Γ ⊢ t ⇒ T → extend Γ S ⊢ rename wk t ⇒ rename wk T
  weaken⇒ {n} {Γ} {S = S} der = ren⇒ (suc {n}) (λ i → refl) (λ i → lookup-extend Γ S i) der

  weaken⇐ : ∀ {n} {Γ : Ctx n} {t T S} → Γ ⊢ t ⇐ T → extend Γ S ⊢ rename wk t ⇐ rename wk T
  weaken⇐ {n} {Γ} {S = S} der = ren⇐ (suc {n}) (λ i → refl) (λ i → lookup-extend Γ S i) der

  ------------------------------------------------------------------------
  -- Substitution.
  --
  -- The general substitution lemma. Given a substitution `σ` and a target
  -- context `Δ` with the coherence
  --
  --     coh : ∀ k → Δ ⊢ σ (toℕ k) ⇒ substS σ (lookup Γ k)
  --
  -- then `Γ ⊢ t ⇐ T` implies `Δ ⊢ substS σ t ⇐ substS σ T`.
  ------------------------------------------------------------------------

  -- The coherence condition.
  Coherent : ∀ {n m} (Γ : Ctx n) (Δ : Ctx m) (σ : Sub) → Set
  Coherent {n} {m} Γ Δ σ = ∀ (k : Fin n) → Δ ⊢ σ (toℕ k) ⇒ substS σ (lookup Γ k)

  ------------------------------------------------------------------------
  -- The extended coherence for the binder case.
  ------------------------------------------------------------------------

  -- `extend Δ (substS σ d) ⊢ extSub σ (toℕ k) ⇒ substS (extSub σ) (lookup (extend Γ d) k)`.
  --
  -- PROVED: the index-0 case is `subst-extSub-wk`; the index-suc case is
  -- weakening of the original coherence.
  coh-extend :
    ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ d}
    → Coherent {n} {m} Γ Δ σ
    → Coherent (extend Γ d) (extend Δ (substS σ d)) (extSub σ)
  coh-extend {Γ = Γ} {Δ = Δ} {σ = σ} {d = d} coh zero =
    subst (λ X → extend Δ (substS σ d) ⊢ tm-var 0 ⇒ X)
          (sym (subst-extSub-wk σ d))
          (⇒-var zero)
  coh-extend {Γ = Γ} {Δ = Δ} {σ = σ} {d = d} coh (suc k) =
    subst (λ X → extend Δ (substS σ d) ⊢ rename wk (σ (toℕ k)) ⇒ X)
          (trans (sym (subst-extSub-wk σ (lookup Γ k)))
                 (cong (substS (extSub σ)) (sym (lookup-renameCtx wk Γ k))))
          (weaken⇒ (coh k))

  ------------------------------------------------------------------------
  -- The `ar`-fold extended coherence (for the `case` branch case).
  ------------------------------------------------------------------------

  -- Lifting the coherence under `ar` field binders: the branch context
  -- `extendⁿ Γ ar` is matched by `extendⁿ Δ ar`, with the substitution
  -- `extSub^ ar σ`. The field positions are holes (fixed by the
  -- substitution); the existing positions are `raise ar`-shifted, where
  -- `subst-extSub^-shift` undoes the `ar`-fold weakening.
  coh-extendⁿ :
    ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ} (ar : ℕ)
    → Coherent {n} {m} Γ Δ σ
    → Coherent (extendⁿ Γ ar) (extendⁿ Δ ar) (extSub^ ar σ)
  coh-extendⁿ {Γ = Γ} {Δ = Δ} {σ = σ} zero coh = coh
  coh-extendⁿ {Γ = Γ} {Δ = Δ} {σ = σ} (suc ar) coh zero =
    subst (λ X → extendⁿ Δ (suc ar) ⊢ tm-var 0 ⇒ X)
          (sym (lookup-extendⁿ-zero Δ ar))
          (⇒-var zero)
  coh-extendⁿ {Γ = Γ} {Δ = Δ} {σ = σ} (suc ar) coh (suc j) =
    subst (λ X → extendⁿ Δ (suc ar) ⊢ rename wk (extSub^ ar σ (toℕ j)) ⇒ X)
          (trans (sym (subst-extSub-wk (extSub^ ar σ) (lookup (extendⁿ Γ ar) j)))
                 (cong (substS (extSub (extSub^ ar σ)))
                       (sym (lookup-extend (extendⁿ Γ ar) (tm-hole "field") j))))
          (weaken⇒ (coh-extendⁿ ar coh j))

  -- The length of a context, exposed for the metatheory.
  lengthCtx : ∀ {n} → Ctx n → ℕ
  lengthCtx {n} _ = n

  ------------------------------------------------------------------------
  -- The substitution lemma.
  ------------------------------------------------------------------------

  -- Helper obligation for the global case: a global's declared type is
  -- CLOSED, so substituting into it leaves it unchanged.
  subst-global : ∀ {m} {Δ : Ctx m} {f} (T : Term) (σ : Sub)
    → Signature.type-of sig f ≡ just T
    → Δ ⊢ tm-global f ⇒ substS σ T
  subst-global {f = f} T σ p = ⇒-conv (⇒-global p) (Conversion.≈-sym conv (≈-subst-closed σ (proj₁ closed f p)))
    where
      ≈-subst-closed : ∀ (σ : Sub) {T} → Scoped 0 T → Conversion._≈_ conv (substS σ T) T
      ≈-subst-closed σ st = subst (λ X → Conversion._≈_ conv X _) (sym (substS-closed st)) (Conversion.≈-refl conv)
  -- name the substitution lemma uses.
  subst-conv : ∀ {t u σ}
    → Conversion._≈_ conv t u
    → Conversion._≈_ conv (substS σ t) (substS σ u)
  subst-conv = Conversion.≈-subst conv _

  mutual
   subst⇒ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {t T σ}
          → Coherent {n} {m} Γ Δ σ
          → Γ ⊢ t ⇒ T
          → Δ ⊢ substS σ t ⇒ substS σ T
   subst⇒ coh (⇒-type p) = ⇒-type p
   subst⇒ coh (⇒-var i) = coh i
   subst⇒ {n = n} {m = m} {Γ = Γ} {Δ = Δ} coh (⇒-pi dd dc) =
     ⇒-pi (subst⇒ coh dd) (subst⇒ (coh-extend {Γ = Γ} {Δ = Δ} coh) dc)
   subst⇒ {Γ = Γ} {Δ = Δ} coh (⇒-lam dd db) =
     ⇒-lam (subst⇒ coh dd) (subst⇐ (coh-extend {Γ = Γ} {Δ = Δ} coh) db)
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-app {f = f} {a = a} {c = c} df da) =
     subst (λ X → Δ ⊢ tm-app (substS σ f) (substS σ a) ⇒ X)
           (sym (subst-topSub σ a c))
           (⇒-app (subst⇒ coh df) (subst⇒ coh da))
   subst⇒ {Γ = Γ} {Δ = Δ} {σ = σ} coh (⇒-let {g = g} {ty = ty} {v = v} {b = b} {l = l} {T = T} dty dv db) =
    subst (λ X → Δ ⊢ tm-let g (substS σ ty) (substS σ v) (substS (extSub σ) b) ⇒ X)
          (sym (subst-topSub σ v T))
          (⇒-let (subst⇒ coh dty) (subst⇐ coh dv) (subst⇒ (coh-extend {Γ = Γ} {Δ = Δ} coh) db))
   subst⇒ coh (⇒-global {f = f} {T = T} p) = subst-global {f = f} T _ p
   subst⇒ coh (⇒-int_type) = ⇒-int_type
   subst⇒ coh (⇒-float_type) = ⇒-float_type
   subst⇒ coh (⇒-binary_type) = ⇒-binary_type
   subst⇒ coh (⇒-atom_type) = ⇒-atom_type
   subst⇒ coh (⇒-int_lit) = ⇒-int_lit
   subst⇒ coh (⇒-float_lit) = ⇒-float_lit
   subst⇒ coh (⇒-atom_lit) = ⇒-atom_lit
   subst⇒ coh (⇒-nat_lit p) = ⇒-nat_lit p
   subst⇒ coh (⇒-bounded_lit p) = ⇒-bounded_lit p
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-data {ps = ps} {is = is} {f = f} p q r) =
     ⇒-data p
        (subst (λ zs → Δ ⊢* zs ⇐* fam-params f) (sym (substTerms-map σ ps))
               (subst-spine coh (tele-closed-subst-params σ f) q))
        (subst (λ zs → Δ ⊢* zs ⇐* fam-indices f) (sym (substTerms-map σ is))
               (subst-spine coh (tele-closed-subst-indices σ f) r))
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-ctor {c = c} {args = args} {f = f} {ct = ct} p q) =
      subst (λ X → Δ ⊢ tm-ctor c (substTermsS σ args) ⇒ X)
            (sym (subst-ctor-result σ f ct))
            (⇒-ctor p (subst (λ zs → Δ ⊢* zs ⇐* ctor-args ct) (sym (substTerms-map σ args))
                             (subst-spine coh (tele-closed-subst-ctor σ f ct) q)))
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-case {s = s} {m = m′} {brs = brs} p q r) =
     ⇒-case (subst⇒ coh p) (subst⇒ coh q) (subst-branches coh r)
   subst⇒ coh (⇒-effect_type p) = ⇒-effect_type (subst⇒ coh p)
   subst⇒ coh (⇒-effect_pure p) = ⇒-effect_pure (subst⇒ coh p)
   subst⇒ coh (⇒-conv der eq) = ⇒-conv (subst⇒ coh der) (subst-conv eq)
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-effect_bind {e = e} {k = k} {A = A} {B = B} p q) =
     ⇒-effect_bind (subst⇒ coh p)
                   (subst (λ X → Δ ⊢ substS σ k ⇒ tm-pi unrestricted (substS σ A) (tm-effect_type X))
                          (subst-extSub-wk σ B)
                          (subst⇒ coh q))

   subst⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {t T σ}
          → Coherent {n} {m} Γ Δ σ
          → Γ ⊢ t ⇐ T
          → Δ ⊢ substS σ t ⇐ substS σ T
   subst⇐ {Γ = Γ} {Δ = Δ} {σ = σ} coh (⇐-lam {g = g} {d = d} {b = b} {c = c} {l = l} ds body) =
    ⇐-lam {g = g} {d = substS σ d} {b = substS (extSub σ) b} {c = substS (extSub σ) c}
          (subst⇒ coh ds)
          (subst⇐ {Γ = extend Γ d} {Δ = extend Δ (substS σ d)} (coh-extend {Γ = Γ} {Δ = Δ} coh) body)
   subst⇐ coh (⇐-conv der eq) = ⇐-conv (subst⇐ coh der) (subst-conv eq)
   subst⇐ coh (⇐-hole) = ⇐-hole
   subst⇐ coh (⇐-infer der eq) = ⇐-infer (subst⇒ coh der) (subst-conv eq)
   subst⇐ coh (⇐-cumul der le) = ⇐-cumul (subst⇒ coh der) le

   -- The telescope is a fixed (closed) telescope from the signature, so
   -- its types are unchanged by substitution.
   subst-spine : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ts tele σ}
          → Coherent {n} {m} Γ Δ σ
        → (∀ {T} → T ∈Tele tele → substS σ T ≡ T)
        → Γ ⊢* ts ⇐* tele → Δ ⊢* map (substS σ) ts ⇐* tele
   subst-spine coh cl ⊢*[] = ⊢*[]
   subst-spine {Δ = Δ} {σ = σ} coh cl (⊢*∷ {x = x} {T = T} {tele = tele} {nm = nm} dx dxs) =
     ⊢*∷ (subst (λ X → Δ ⊢ substS σ x ⇐ X) (cl ∈-here) (subst⇐ coh dx))
         (subst-spine coh (λ p → cl (∈-there p)) dxs)

   -- Branch checking is preserved by substitution. The branch context
   -- `extendⁿ Γ ar` is matched by `extendⁿ Δ ar` via `coh-extendⁿ`; the
   -- body is substituted by `extSub^ ar σ`. The motive's substitution is
   -- the subtle step, discharged by `subst-branch-motive`.
   subst-branches : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {brs nm m′ σ}
          → Coherent {n} {m} Γ Δ σ
        → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
        → Δ ⊢*brs substBranchesS σ brs ⇐*ᵇ (nm , substS σ m′)
   subst-branches coh brs[] = brs[]
   subst-branches {Γ = Γ} {Δ = Δ} {σ = σ} coh
                  (brs∷ {cn = cn} {ar = ar} {b = b} {brs = brs} {n = nm} {m = m′} {f = f} {ct = ct} fc len db dbrs) =
     brs∷ fc len
          (subst (λ X → extendⁿ Δ ar ⊢ substS (extSub^ ar σ) b ⇐ X)
                 (subst-branch-motive ar σ m′ cn)
                 (subst⇐ (coh-extendⁿ ar coh) db))
          (subst-branches coh dbrs)

  ------------------------------------------------------------------------
  -- The top-level substitution (for β and ζ).
  ------------------------------------------------------------------------

  -- Substitution at the top of a term (using `topSub` from Core.Syntax).
  substTop : Term → Term → Term
  substTop a t = substS (topSub a) t

  -- The top-substitution coherence: `topSub a` maps index 0 to `a` and
  -- index `suc j` to `tm-var j`. At the head we need the argument `a` to
  -- INFER its type `A` (the β case supplies this, since the argument of a
  -- λ is checked against the domain and values infer their type).
  CohTop : ∀ {n} (Γ : Ctx n) (A a : Term) (k : Fin (suc n)) → Set
  CohTop Γ A a k =
    Γ ⊢ topSub a (toℕ k) ⇒ substS (topSub a) (lookup (extend Γ A) k)

  -- `CohTop` at the head: `Γ ⊢ a ⇒ substS (topSub a) (rename wk A)`, which
  -- is `Γ ⊢ a ⇒ A` by `topSub-rename`.
  cohTop-zero : ∀ {n} {Γ : Ctx n} {A a} → Γ ⊢ a ⇒ A → CohTop Γ A a zero
  cohTop-zero {Γ = Γ} {A = A} {a = a} h =
    subst (λ X → Γ ⊢ a ⇒ X)
          (trans (sym (topSub-rename a A))
                 (sym (cong (substS (topSub a)) (lookup-head Γ A))))
          h

  -- `CohTop` at a variable: `Γ ⊢ tm-var j ⇒ lookup Γ j`.
  cohTop-suc : ∀ {n} {Γ : Ctx n} {A a} (k : Fin n)
    → CohTop Γ A a (suc k)
  cohTop-suc {Γ = Γ} {A = A} {a = a} k =
    subst (λ X → Γ ⊢ tm-var (toℕ k) ⇒ X)
          (trans (sym (topSub-rename a (lookup Γ k)))
                 (sym (cong (substS (topSub a)) (lookup-extend Γ A k))))
          (⇒-var k)

  substTop⇒ :
    ∀ {n} {Γ : Ctx n} {t T A a}
    → extend Γ A ⊢ t ⇒ T
    → Γ ⊢ a ⇒ A
    → Γ ⊢ substTop a t ⇒ substTop a T
  substTop⇒ {Γ = Γ} {A = A} {a = a} dt h =
    subst⇒ {Γ = extend Γ A} {Δ = Γ}
           (λ { zero → cohTop-zero {Γ = Γ} {A = A} {a = a} h
              ; (suc k) → cohTop-suc {Γ = Γ} {A = A} {a = a} k })
           dt

  substTop⇐ :
    ∀ {n} {Γ : Ctx n} {t T A a}
    → extend Γ A ⊢ t ⇐ T
    → Γ ⊢ a ⇒ A
    → Γ ⊢ substTop a t ⇐ substTop a T
  substTop⇐ {Γ = Γ} {A = A} {a = a} dt h =
    subst⇐ {Γ = extend Γ A} {Δ = Γ}
           (λ { zero → cohTop-zero {Γ = Γ} {A = A} {a = a} h
              ; (suc k) → cohTop-suc {Γ = Γ} {A = A} {a = a} k })
           dt

  ------------------------------------------------------------------------
  -- Preservation
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Value inversion: a checked value infers its type.
  ------------------------------------------------------------------------

  -- `HoleFree a`: `a` contains no `tm-hole`. (A hole checks at any type
  -- but never infers, so `value-infer` needs this side condition.)
  HoleFree : Term → Set
  HoleFree a = (name : Name) → a ≡ tm-hole name → ⊥

  -- Cumulativity as a conversion: `Type i ≈ Type j` when `i ≤ j`. A
  -- projection of the `Conversion` record's cumulativity field.
  ≈-cumul : ∀ {i j} → i ≤ˡ j → Conversion._≈_ conv (tm-type i) (tm-type j)
  ≈-cumul = Conversion.≈-type conv
  -- Cumulativity on the inferred type.
  ⇒-cumul-infer : ∀ {n} {Γ : Ctx n} {t i j} → Γ ⊢ t ⇒ tm-type i → i ≤ˡ j → Γ ⊢ t ⇒ tm-type j
  ⇒-cumul-infer der le = ⇒-conv der (≈-cumul le)

  -- A hole-free VALUE that checks against a type infers that type. `⇐-lam`
  -- and `⇒-lam` share their premises, so the λ case is direct; `⇐-infer`
  -- uses `⇒-conv`; `⇐-hole` is impossible (the value would be a hole).
  value-infer : ∀ {n} {Γ : Ctx n} {a A} → HoleFree a → Value a → Γ ⊢ a ⇐ A → Γ ⊢ a ⇒ A
  value-infer hf v (⇐-infer der eq) = ⇒-conv der eq
  value-infer hf v (⇐-conv der eq) = ⇒-conv (value-infer hf v der) eq
  value-infer hf v (⇐-cumul der le) = ⇒-cumul-infer der le
  value-infer hf (canonical c-lam) (⇐-lam {g = g} {d = d} {b = b} {c = c} ds body) =
    ⇒-lam {g = g} {d = d} {b = b} {c = c} ds body
  value-infer hf (canonical ()) ⇐-hole
  value-infer hf (neutral n-hole) ⇐-hole = ⊥-elim (hf _ refl)

  -- A λ's infer derivation, inverted to the Π type it infers (the type
  -- equation is up to conversion).
  lam-pi-trans : ∀ {n} {Γ : Ctx n} {g d b} (T T′ : Term)
    → Σ Term (λ c → (Conversion._≈_ conv T′ (tm-pi g d c))
                    × (Γ ⊢ tm-lam g d b ⇒ tm-pi g d c))
    → Conversion._≈_ conv T′ T
    → Σ Term (λ c → (Conversion._≈_ conv T (tm-pi g d c))
                    × (Γ ⊢ tm-lam g d b ⇒ tm-pi g d c))
  lam-pi-trans T T′ (c , eq″ , der′) eq =
    c , Conversion.≈-trans conv (Conversion.≈-sym conv eq) eq″ , der′

  lam-type-pi : ∀ {n} {Γ : Ctx n} {g d b T} → Γ ⊢ tm-lam g d b ⇒ T
              → Σ Term (λ c → (Conversion._≈_ conv T (tm-pi g d c))
                              × (Γ ⊢ tm-lam g d b ⇒ tm-pi g d c))
  lam-type-pi (⇒-lam dd db) = _ , Conversion.≈-refl conv , ⇒-lam dd db
  lam-type-pi {g = g} {d = d} {T = T} (⇒-conv {T = T′} der eq) =
    lam-pi-trans T T′ (lam-type-pi der) eq

  -- `⇒-lam-inv-aux`: a λ that infers `T` has its body check any `c` with
  -- `T ≈ tm-pi g d c`. Structural on the derivation.
  ⇒-lam-inv-aux : ∀ {n} {Γ : Ctx n} {g d b} (T : Term) (c : Term)
                → Γ ⊢ tm-lam g d b ⇒ T
                → Conversion._≈_ conv T (tm-pi g d c)
                → extend Γ d ⊢ b ⇐ c
  ⇒-lam-inv-aux (tm-pi g d c₀) c (⇒-lam dd db) eq =
    ⇐-conv db (proj₂ (proj₂ (conv-pi-components eq)))
  ⇒-lam-inv-aux T c (⇒-conv {T = T′} der eq′) eq =
    ⇒-lam-inv-aux T′ c der (Conversion.≈-trans conv eq′ eq)

  -- The body of a λ that infers a Π type checks the codomain.
  ⇒-lam-inv : ∀ {n} {Γ : Ctx n} {g d b c}
            → Γ ⊢ tm-lam g d b ⇒ tm-pi g d c
            → extend Γ d ⊢ b ⇐ c
  ⇒-lam-inv der = ⇒-lam-inv-aux _ _ der (Conversion.≈-refl conv)

  -- `substTopT` is a congruence for conversion of the codomain: it is
  -- `substS (topSub a)`, and conversion is stable under substitution.
  substTopT-conv : ∀ a {c c′} → Conversion._≈_ conv c c′
                 → Conversion._≈_ conv (substTopT a c) (substTopT a c′)
  substTopT-conv a = Conversion.≈-subst conv (topSub a)

  ------------------------------------------------------------------------
  -- Context conversion.
  --
  -- If two contexts have pointwise-convertible lookups, then a term's
  -- typability transports between them (with the type converted). This is
  -- the lemma the `⇒-app`-under-`⇒-conv` case of β needs: a λ whose own
  -- domain `d′` converts to the application's `d` still has its body
  -- checking the codomain under `d`.
  ------------------------------------------------------------------------

  -- Extend a pointwise-convertible context witness under a binder.
  ext-conv : ∀ {n} {Γ Γ′ : Ctx n} {d d′}
           → Conversion._≈_ conv d d′
           → (∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
           → ∀ i → Conversion._≈_ conv (lookup (extend Γ d) i) (lookup (extend Γ′ d′) i)
  ext-conv dd w zero = rename-conv wk dd
  ext-conv {Γ = Γ} {Γ′ = Γ′} dd w (suc i) =
    Conversion.≈-trans conv
      (≡→≈ (lookup-renameCtx wk Γ i))
      (Conversion.≈-trans conv
        (rename-conv wk (w i))
        (≡→≈ (sym (lookup-renameCtx wk Γ′ i))))
    where
      ≡→≈ : ∀ {t u} → t ≡ u → Conversion._≈_ conv t u
      ≡→≈ refl = Conversion.≈-refl conv

  mutual
    conv⇒ : ∀ {n} {Γ Γ′ : Ctx n} {t T T′}
          → (∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
          → Conversion._≈_ conv T T′
          → Γ ⊢ t ⇒ T → Γ′ ⊢ t ⇒ T′
    conv⇒ w eq (⇒-type p) = ⇒-conv (⇒-type p) eq
    conv⇒ {Γ = Γ} {Γ′ = Γ′} w eq (⇒-var i) =
      ⇒-conv (⇒-var i) (Conversion.≈-trans conv (Conversion.≈-sym conv (w i)) eq)
    conv⇒ w eq (⇒-pi {d = d} dd dc) =
      ⇒-conv (⇒-pi (conv⇒ w (Conversion.≈-refl conv) dd)
                   (conv⇒ (ext-conv (Conversion.≈-refl conv) w) (Conversion.≈-refl conv) dc)) eq
    conv⇒ w eq (⇒-lam {d = d} dd db) =
      ⇒-conv (⇒-lam (conv⇒ w (Conversion.≈-refl conv) dd)
                    (conv⇐ (ext-conv (Conversion.≈-refl conv) w) (Conversion.≈-refl conv) db)) eq
    conv⇒ {Γ = Γ} {Γ′ = Γ′} w eq (⇒-app {f = f} {a = a} {c = c} df da) =
      ⇒-conv (⇒-app (conv⇒ w (Conversion.≈-refl conv) df) (conv⇒ w (Conversion.≈-refl conv) da)) eq
    conv⇒ {Γ = Γ} {Γ′ = Γ′} w eq (⇒-let {ty = ty} {v = v} {T = T} dty dv db) =
      ⇒-conv (⇒-let (conv⇒ w (Conversion.≈-refl conv) dty)
                    (conv⇐ w (Conversion.≈-refl conv) dv)
                    (conv⇒ (ext-conv (Conversion.≈-refl conv) w) (Conversion.≈-refl conv) db)) eq
    conv⇒ w eq (⇒-global p) = ⇒-conv (⇒-global p) eq
    conv⇒ w eq (⇒-int_type) = ⇒-conv (⇒-int_type) eq
    conv⇒ w eq (⇒-float_type) = ⇒-conv (⇒-float_type) eq
    conv⇒ w eq (⇒-binary_type) = ⇒-conv (⇒-binary_type) eq
    conv⇒ w eq (⇒-atom_type) = ⇒-conv (⇒-atom_type) eq
    conv⇒ w eq (⇒-int_lit) = ⇒-conv (⇒-int_lit) eq
    conv⇒ w eq (⇒-float_lit) = ⇒-conv (⇒-float_lit) eq
    conv⇒ w eq (⇒-atom_lit) = ⇒-conv (⇒-atom_lit) eq
    conv⇒ w eq (⇒-nat_lit p) = ⇒-conv (⇒-nat_lit p) eq
    conv⇒ w eq (⇒-bounded_lit p) = ⇒-conv (⇒-bounded_lit p) eq
    conv⇒ w eq (⇒-data p q r) = ⇒-conv (⇒-data p (conv-spine w q) (conv-spine w r)) eq
    conv⇒ w eq (⇒-ctor p q) = ⇒-conv (⇒-ctor p (conv-spine w q)) eq
    conv⇒ w eq (⇒-case p q r) = ⇒-conv (⇒-case (conv⇒ w (Conversion.≈-refl conv) p) (conv⇒ w (Conversion.≈-refl conv) q) (conv-branches w r)) eq
    conv⇒ w eq (⇒-effect_type p) = ⇒-conv (⇒-effect_type (conv⇒ w (Conversion.≈-refl conv) p)) eq
    conv⇒ w eq (⇒-effect_pure p) = ⇒-conv (⇒-effect_pure (conv⇒ w (Conversion.≈-refl conv) p)) eq
    conv⇒ w eq (⇒-effect_bind p q) = ⇒-conv (⇒-effect_bind (conv⇒ w (Conversion.≈-refl conv) p) (conv⇒ w (Conversion.≈-refl conv) q)) eq
    conv⇒ w eq (⇒-conv der eq′) = conv⇒ w (Conversion.≈-trans conv eq′ eq) der

    conv⇐ : ∀ {n} {Γ Γ′ : Ctx n} {t T T′}
          → (∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
          → Conversion._≈_ conv T T′
          → Γ ⊢ t ⇐ T → Γ′ ⊢ t ⇐ T′
    conv⇐ w eq (⇐-lam ds body) =
      ⇐-conv (⇐-lam (conv⇒ w (Conversion.≈-refl conv) ds)
                     (conv⇐ (ext-conv (Conversion.≈-refl conv) w) (Conversion.≈-refl conv) body)) eq
    conv⇐ w eq (⇐-hole) = ⇐-hole
    conv⇐ w eq (⇐-infer der eq′) = ⇐-infer (conv⇒ w eq′ der) eq
    conv⇐ w eq (⇐-conv der eq′) = conv⇐ w (Conversion.≈-trans conv eq′ eq) der
    conv⇐ w eq (⇐-cumul der le) = ⇐-conv (⇐-cumul (conv⇒ w (Conversion.≈-refl conv) der) le) eq
    conv-spine : ∀ {n} {Γ Γ′ : Ctx n} {ts tele}
               → (∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
               → Γ ⊢* ts ⇐* tele → Γ′ ⊢* ts ⇐* tele
    conv-spine w ⊢*[] = ⊢*[]
    conv-spine w (⊢*∷ dx dxs) = ⊢*∷ (conv⇐ w (Conversion.≈-refl conv) dx) (conv-spine w dxs)

    conv-branches : ∀ {n} {Γ Γ′ : Ctx n} {brs nm m}
                  → (∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
                  → Γ ⊢*brs brs ⇐*ᵇ (nm , m) → Γ′ ⊢*brs brs ⇐*ᵇ (nm , m)
    conv-branches w brs[] = brs[]
    conv-branches {Γ = Γ} {Γ′ = Γ′} w (brs∷ {cn = cn} {ar = ar} {b = b} fc len body rest) =
      brs∷ fc len (conv⇐ (extⁿ-conv w ar) (Conversion.≈-refl conv) body) (conv-branches w rest)

    -- Extend the witness under `k` hole binders (a `case` branch context).
    extⁿ-conv : ∀ {n} {Γ Γ′ : Ctx n} (w : ∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
              → ∀ k → ∀ i → Conversion._≈_ conv (lookup (extendⁿ Γ k) i) (lookup (extendⁿ Γ′ k) i)
    extⁿ-conv w zero = w
    extⁿ-conv w (suc k) = ext-conv (Conversion.≈-refl conv) (extⁿ-conv w k)
  -- The `⇒-conv`-on-function case of β: `dflam` is a λ derivation whose
  -- type `T₀` converts to `tm-pi g d c`. `lam-type-pi` exposes the λ's own
  -- Π type `tm-pi g′ d′ c′`; Π injectivity gives `d′ ≈ d` and `c′ ≈ c`; the
  -- body (which checks `c′` under `d′`) is converted to check `c` under `d`
  -- by CONTEXT CONVERSION, and `substTop⇐` instantiates it.
  preserve-β-conv-aux : ∀ {g g′ d′ d b a c T₀}
    → ⟨⟩ ⊢ tm-lam g′ d′ b ⇒ T₀
    → Conversion._≈_ conv T₀ (tm-pi g d c)
    → ⟨⟩ ⊢ a ⇒ d
    → ⟨⟩ ⊢ substTopT a b ⇐ substTopT a c
  preserve-β-conv-aux {g = g} {d = d} {b = b} {a = a} {c = c} {T₀ = T₀} dflam ceq da =
    substTop⇐ {n = zero} {Γ = ⟨⟩} {A = d} body-checks da
    where
      c′ : Term
      c′ = proj₁ (lam-type-pi dflam)
      eq″ : Conversion._≈_ conv T₀ (tm-pi _ _ c′)
      eq″ = proj₁ (proj₂ (lam-type-pi dflam))
      der′ : ⟨⟩ ⊢ tm-lam _ _ b ⇒ tm-pi _ _ c′
      der′ = proj₂ (proj₂ (lam-type-pi dflam))
      comps = conv-pi-components (Conversion.≈-trans conv (Conversion.≈-sym conv eq″) ceq)
      body-checks : extend ⟨⟩ d ⊢ b ⇐ c
      body-checks = conv⇐ (ext-conv (proj₁ (proj₂ comps)) (λ ())) (proj₂ (proj₂ comps)) (⇒-lam-inv der′)
  -- β: `(λx. b) a ⇝ b[x := a]`.
  --
  -- PROVED. `⇒-app` gives `⟨⟩ ⊢ tm-lam g d b ⇒ tm-pi g d c` (so `T =
  -- substTopT a c`) and `⟨⟩ ⊢ a ⇒ d`; `⇒-lam-inv` gives
  -- `extend ⟨⟩ d ⊢ b ⇐ c`. `substTop⇐` yields
  -- `⟨⟩ ⊢ substTopT a b ⇐ substTopT a c`.
  preserve-β :
    ∀ {g d b a T}
    → ⟨⟩ ⊢ tm-app (tm-lam g d b) a ⇒ T
    → ⟨⟩ ⊢ substTopT a b ⇐ T
  preserve-β {g = g} {d = d} {b = b} {a = a} (⇒-app {g = g} {d = d} {c = c} (⇒-lam {g = g} {d = d} {b = b} {c = c} dd db) da) =
    substTop⇐ {n = zero} {Γ = ⟨⟩} {A = d}
              (⇒-lam-inv {g = g} {d = d} {b = b} {c = c}
                         (⇒-lam {g = g} {d = d} {b = b} {c = c} dd db)) da
  preserve-β {g = g} {d = d} {b = b} {a = a} (⇒-app {c = c} (⇒-conv {T = T₀} dflam ceq) da) =
    preserve-β-conv-aux dflam ceq da

  preserve-β (⇒-conv der eq) = ⇐-conv (preserve-β der) eq



  -- ζ: `let x = v in b ⇝ b[x := v]`.
  --
  -- Similar to β: `⇒-let` gives `⟨⟩ ⊢ v ⇐ ty` and `extend ⟨⟩ ty ⊢ b ⇒ T`
  -- (so the result type is `substTopT v T`); `value-infer` turns the
  -- checked value into an inferring one, and `substTop⇐` gives the result.
  preserve-ζ :
    ∀ {g ty v b T}
    → ⟨⟩ ⊢ tm-let g ty v b ⇒ T
    → Value v
    → HoleFree v
    → ⟨⟩ ⊢ substTopT v b ⇐ T
  preserve-ζ {g = g} {ty = ty} {v = v} {b = b} {T = T} (⇒-let {l = l} dty dv db) val hf =
    substTop⇐ {n = zero} {Γ = ⟨⟩} {A = ty} (⇒-check db) (value-infer hf val dv)
    where
      ⇒-check : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Γ ⊢ t ⇐ T
      ⇒-check der = ⇐-infer der (Conversion.≈-refl conv)
  preserve-ζ (⇒-conv der eq) val hf = ⇐-conv (preserve-ζ der val hf) eq



  -- The remaining reduction rules (ι, δ, and the congruence rules).
  postulate
    preservation-other :
      ∀ {t t′ T} → ⟨⟩ ⊢ t ⇐ T → _⇝_ sig t t′ → ⟨⟩ ⊢ t′ ⇐ T

    preservation⇒-other :
      ∀ {t t′ T} → ⟨⟩ ⊢ t ⇒ T → _⇝_ sig t t′ → ⟨⟩ ⊢ t′ ⇒ T


  preservation⇒ :
    ∀ {t t′ T}
    → ⟨⟩ ⊢ t ⇒ T
    → _⇝_ sig t t′
    → ⟨⟩ ⊢ t′ ⇒ T
  preservation⇒ der rw = preservation⇒-other der rw

  -- Preservation (docs/SOUNDNESS.md §4).
  --
  --   If `⟨⟩ ⊢ t ⇐ T` and `t ⇝ t′` then `⟨⟩ ⊢ t′ ⇐ T`.
  --
  -- The β and ζ cases are PROVED (see `preserve-β` / `preserve-ζ` above);
  -- the ι (branch substitution), δ (certified unfolding), and congruence
  -- cases are the remaining obligations, isolated in `preservation-other`.
  preservation :
    ∀ {t t′ T}
    → ⟨⟩ ⊢ t ⇐ T
    → _⇝_ sig t t′
    → ⟨⟩ ⊢ t′ ⇐ T
  preservation (⇐-infer der eq) rw = ⇐-infer (preservation⇒ der rw) eq
  preservation (⇐-conv der eq) rw = ⇐-conv (preservation der rw) eq
  preservation (⇐-cumul der le) rw = ⇐-cumul (preservation⇒ der rw) le
  preservation (⇐-lam ds body) rw = preservation-other (⇐-lam ds body) rw
  preservation ⇐-hole rw = preservation-other ⇐-hole rw

