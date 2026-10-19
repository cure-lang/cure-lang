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
-- STATUS: the explicit closed-telescope fragment uses the inhabited,
-- membership-indexed ClosedFragmentSig invariant. This does NOT cover
-- genuinely dependent telescope entries. Proof.ReductionConversion
-- supplies full formal ReduceConv; Proof.SoundnessModel jointly inhabits
-- all current hypotheses. This is a closed-entry specification theorem,
-- not an executable NbE/refinement or full dependent Cure certificate.
------------------------------------------------------------------------
module Proof.Preservation where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm)
open import Function using (_∘_)
open import Data.Fin using (Fin; zero; suc; toℕ; cast)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List using () renaming (lookup to listLookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
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
                                   ctor-args; ctor-params; ctor-indices; just-inj)
open import Core.Reduction
open import Core.Coverage
open import Core.ClosedFragment public using (ClosedFragmentSig; family-lookup-member)
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; lookup-extend; lookup-renameCtx; renameCtx; Conversion; extendⁿ; extendTele; teleField; fieldFin; listLookup-∈Tele; branch-field-vars; upto; _∈Tele_; ∈-here; ∈-there)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Progress using (Final; FinalTerms; FinalBranches; BuiltinCtors; Certified;
                                    f-type; f-var; f-pi; f-lam; f-let; f-app;
                                    f-data; f-ctor; f-case; f-global;
                                    f-int_type; f-int_lit; f-nat_lit; f-bounded_lit;
                                    f-float_type; f-float_lit; f-binary_type;
                                    f-atom_type; f-atom_lit;
                                    f-effect_type; f-effect_pure; f-effect_bind;
                                    ft[]; ft∷; fb[]; fb∷)
open import Proof.Inversion
open import Proof.Substitution
open import Proof.FinalPreservation using (final-preservation)
open import Proof.Context using (lookup-weaken; lookup-head;
                                  lookup-extendⁿ-zero; lookup-extendⁿ-raise;
                                  extF; extF-coh; lookup-extF;
                                  lookup-extendTele-field; lookup-extendTele-raise;
                                  extF-tele; extF-tele-coh; lookup-extF-tele)

------------------------------------------------------------------------
-- Signature closedness.
--
-- Core.ClosedFragment constrains only actual signature members. Individual
-- entries/results are still closed, because the current spine/context
-- proofs require rename/substitution identity. This is an explicit
-- fragment restriction, not a proof of well-scoped dependent telescopes.
-- Migrating ScopedSignature together with dependent typing remains open.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- The well-typedness half of the totality certificate.
--
-- `Certified` (Proof.Progress) says a certified global's body is FINAL.
-- The δ rule also needs the body to INFER the global's declared type — the
-- well-typedness half of the kernel's `Env.certified?`. We carry it as a
-- separate hypothesis (it mentions the typing judgment, which `Certified`
-- cannot, being defined before the judgment). The body is also CLOSED, so
-- the weakening-from-`⟨⟩` transport (`weaken-closed`) types it in any `Γ`.
--
-- Defined at the TOP LEVEL (outside `Preserve`) so the module header can
-- name it.
------------------------------------------------------------------------

CertifiedTyped : (ind : IndEnv) (sig : Signature) (conv : Conversion) → Set
CertifiedTyped ind sig conv =
  ∀ {f body′ T}
  → Signature.body sig f ≡ just body′
  → Signature.type-of sig f ≡ just T
  → Scoped 0 body′ × Core.Typing.Typing._⊢_⇒_ ind sig conv ⟨⟩ body′ T

-- Reduction implies conversion: the kernel's `conv?` normalises both sides,
-- so a one-step reduct is definitionally equal to its redex. This makes the
-- `ξ-*` congruences type-preserving (the result type of `⇒-app` / `⇒-let` /
-- `⇒-case` names the argument SYNTACTICALLY). A hypothesis (not a `Conversion`
-- field) because it mentions the signature-parameterised `_⇝_`.
ReduceConv : Signature → Conversion → Set
ReduceConv sig conv = ∀ {t t′} → _⇝_ sig t t′ → Conversion._≈_ conv t t′

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion)
               (closed : ClosedFragmentSig ind sig) (rc : ReduceConv sig conv)
               (ctyped : CertifiedTyped ind sig conv) (bc : BuiltinCtors ind)
               (cert : Certified sig) where
  open Core.Typing.Typing ind sig conv
  open Proof.Inversion.Invert ind sig conv
    using (conv-pi-components; universe-not-pi; constructor-data;
           nat-data-family; bounded-data-family)

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
  -- ClosedFragmentSig is defined in Core.ClosedFragment. The lemmas below
  -- use actual lookup/membership witnesses to obtain the rename/subst
  -- identity facts required by this closed-entry fragment.
  ------------------------------------------------------------------------

  -- A global's declared type is closed, so renaming leaves it unchanged.
  rename-global-type : ∀ (ρ : Ren) (f : Name) (T : Term)
    → Signature.type-of sig f ≡ just T → rename ρ T ≡ T
  rename-global-type ρ f T p = rename-closed (proj₁ closed f p)

  -- Membership witnesses are mandatory for signature entries. The
  -- fragment still requires individual entries to be closed.
  tele-closed-params : ∀ (ρ : Ren) (f : Family)
    → f ∈ IndEnv.families ind
    → ∀ {T} → T ∈Tele (fam-params f) → rename ρ T ≡ T
  tele-closed-params ρ f member h =
    rename-closed (proj₁ (proj₂ closed) f member h)

  tele-closed-indices : ∀ (ρ : Ren) (f : Family)
    → f ∈ IndEnv.families ind
    → ∀ {T} → T ∈Tele (fam-indices f) → rename ρ T ≡ T
  tele-closed-indices ρ f member h =
    rename-closed (proj₁ (proj₂ (proj₂ closed)) f member h)

  ctor-members : ∀ {c f ct}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → f ∈ IndEnv.families ind × ct ∈ Core.Signature.fam-ctors f
  ctor-members {c} {f} {ct} found
    with lookup-ctor-members {c = c} {fs = IndEnv.families ind} {f = f} {ct = ct} found
  ... | family-member , ctor-member , name = family-member , ctor-member

  ctor-field-closed : ∀ f ct {c T}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → T ∈Tele (ctor-args ct) → Scoped 0 T
  ctor-field-closed f ct {c} found entry
    with ctor-members {c = c} {f = f} {ct = ct} found
  ... | family-member , ctor-member =
    proj₁ (proj₂ (proj₂ (proj₂ closed))) f family-member ct ctor-member entry

  ctor-result-closed : ∀ f ct {c}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → Scoped 0 (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
  ctor-result-closed f ct {c} found
    with ctor-members {c = c} {f = f} {ct = ct} found
  ... | family-member , ctor-member =
    proj₂ (proj₂ (proj₂ (proj₂ closed))) f family-member ct ctor-member

  tele-closed-ctor : ∀ (ρ : Ren) (f : Family) (ct : Ctor) {c}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → ∀ {T} → T ∈Tele (ctor-args ct) → rename ρ T ≡ T
  tele-closed-ctor ρ f ct {c} found h =
    rename-closed (ctor-field-closed f ct {c = c} found h)

  teleField-closed : ∀ (f : Family) (ct : Ctor) {c}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → (j : Fin (length (ctor-args ct))) → Scoped 0 (teleField (ctor-args ct) j)
  teleField-closed f ct {c} found j =
    ctor-field-closed f ct {c = c} found (listLookup-∈Tele (ctor-args ct) j)

  rename-ctor-result : ∀ (ρ : Ren) (f : Family) (ct : Ctor) {c}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → rename ρ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
      ≡ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)
  rename-ctor-result ρ f ct {c} found =
    rename-closed (ctor-result-closed f ct {c = c} found)

  subst-closed : ∀ (σ : Sub) {T : Term} → Scoped 0 T → substS σ T ≡ T
  subst-closed σ st = substS-closed st

  tele-closed-subst-params : ∀ (σ : Sub) (f : Family)
    → f ∈ IndEnv.families ind
    → ∀ {T} → T ∈Tele (fam-params f) → substS σ T ≡ T
  tele-closed-subst-params σ f member h =
    subst-closed σ (proj₁ (proj₂ closed) f member h)

  tele-closed-subst-indices : ∀ (σ : Sub) (f : Family)
    → f ∈ IndEnv.families ind
    → ∀ {T} → T ∈Tele (fam-indices f) → substS σ T ≡ T
  tele-closed-subst-indices σ f member h =
    subst-closed σ (proj₁ (proj₂ (proj₂ closed)) f member h)

  tele-closed-subst-ctor : ∀ (σ : Sub) (f : Family) (ct : Ctor) {c}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → ∀ {T} → T ∈Tele (ctor-args ct) → substS σ T ≡ T
  tele-closed-subst-ctor σ f ct {c} found h =
    subst-closed σ (ctor-field-closed f ct {c = c} found h)

  subst-ctor-result : ∀ (σ : Sub) (f : Family) (ct : Ctor) {c}
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
    → substS σ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
      ≡ tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)
  subst-ctor-result σ f ct {c} found =
    subst-closed σ (ctor-result-closed f ct {c = c} found)

  -- Conversion is a congruence for renaming. This is a field of the
  -- `Conversion` record (Core/Typing.agda). Implementation refinement of
  -- this required law remains open. We re-export it under the local name
  -- the renaming lemma uses.
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
               (ren-spine idx coh law (tele-closed-params ρ f (family-lookup-member {fs = IndEnv.families ind} p)) q))
        (subst (λ zs → Δ ⊢* zs ⇐* fam-indices f) (sym (renameTerms-map ρ is))
               (ren-spine idx coh law (tele-closed-indices ρ f (family-lookup-member {fs = IndEnv.families ind} p)) r))
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-ctor {c = c} {args = args} {f = f} {ct = ct} p q) =
      subst (λ X → Δ ⊢ tm-ctor c (renameTerms ρ args) ⇒ X)
            (sym (rename-ctor-result ρ f ct {c = c} p))
            (⇒-ctor p (subst (λ zs → Δ ⊢* zs ⇐* ctor-args ct) (sym (renameTerms-map ρ args)) (ren-spine idx coh law (tele-closed-ctor ρ f ct {c = c} p) q)))
    ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-case {s = s} {m = m′} {brs = brs} p q r covered) =
      ⇒-case (ren⇒ idx coh law p) (ren⇒ idx coh law q) (ren-branches idx coh law r)
        (case-coverage-rename {brs = brs} ρ covered)
    ren⇒ idx coh law (⇒-effect_type p) = ⇒-effect_type (ren⇒ idx coh law p)
    ren⇒ idx coh law (⇒-effect_pure p) = ⇒-effect_pure (ren⇒ idx coh law p)
    ren⇒ idx coh law (⇒-conv der eq) =
      ⇒-conv (ren⇒ idx coh law der) (rename-conv _ eq)
    ren⇒ idx coh law (⇒-cumul der le) = ⇒-cumul (ren⇒ idx coh law der) le
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
    -- `extendTele Γ (ctor-args ct)` is transported by the telescope morphism
    -- `extF-tele (ctor-args ct) idx`; the body is renamed by
    -- `ext^ (length (ctor-args ct)) ρ`. The motive's renaming is the subtle
    -- step: `m′` is used in the extended context, so renaming it under
    -- `ext^ (length (ctor-args ct)) ρ` agrees with renaming it under `ρ`
    -- because the field indices are fixed and the existing indices are
    -- `raise`-shifted.
    ren-branches : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {brs nm m′ ρ}
           (idx : Fin n → Fin m)
         → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
         → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
         → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
         → Δ ⊢*brs renameBranches ρ brs ⇐*ᵇ (nm , rename ρ m′)
    ren-branches idx coh law brs[] = brs[]
    ren-branches {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law
                 (brs∷ {cn = cn} {b = b} {brs = brs} {n = nm} {m = m′} {f = f} {ct = ct} fc db dbrs) =
      brs∷ fc
           (subst (λ X → extendTele Δ (ctor-args ct) ⊢ rename (ext^ (length (ctor-args ct)) ρ) b ⇐ X)
                  (rename-branch-motive (length (ctor-args ct)) ρ m′ cn)
                  (ren⇐ {Γ = extendTele Γ (ctor-args ct)} {Δ = extendTele Δ (ctor-args ct)}
                        (extF-tele (ctor-args ct) idx) (extF-tele-coh (ctor-args ct) ρ idx coh)
                  (lookup-extF-tele Γ Δ (ctor-args ct) ρ idx law
                                    (λ j → teleField-closed f ct fc j)) db))
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

  -- Weakening-from-`⟨⟩`: a CLOSED term that types in the empty context types
  -- in any context, because the context morphism `Fin 0 → Fin n` is vacuous
  -- and the renaming is the identity on closed terms. This is what the δ
  -- case needs: a global's body types in `⟨⟩` but must type in `Γ`.
  weaken-closed : ∀ {n} {Γ : Ctx n} {t T}
    → Scoped 0 t → Scoped 0 T → ⟨⟩ ⊢ t ⇒ T → Γ ⊢ t ⇒ T
  weaken-closed {Γ = Γ} {t = t} {T = T} st sT der =
    subst (λ X → Γ ⊢ X ⇒ T) (rename-closed {ρ = λ k → k} st)
          (subst (λ X → Γ ⊢ rename (λ k → k) t ⇒ X) (rename-closed {ρ = λ k → k} sT)
                 (ren⇒ {Γ = ⟨⟩} {Δ = Γ} {ρ = λ k → k} (λ ()) (λ ()) (λ ()) der))

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
  -- The telescope-extended coherence (for the `case` branch case).
  ------------------------------------------------------------------------

  -- Lifting the coherence under the field binders of a constructor's
  -- argument telescope: the branch context `extendTele Γ tele` is matched by
  -- `extendTele Δ tele`, with the substitution `extSub^ (length tele) σ`.
  -- The FIELD positions hold closed telescope entries (fixed by the
  -- substitution); the existing positions are `raise (length tele)`-shifted,
  -- where `subst-extSub^-shift` undoes the `length tele`-fold weakening.
  coh-extendTele :
    ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ} (tele : Telescope)
    → (∀ j → Scoped 0 (teleField tele j))
    → Coherent {n} {m} Γ Δ σ
    → Coherent (extendTele Γ tele) (extendTele Δ tele) (extSub^ (length tele) σ)
  coh-extendTele {Γ = Γ} {Δ = Δ} {σ = σ} [] cl coh = coh
  coh-extendTele {Γ = Γ} {Δ = Δ} {σ = σ} ((nm , T) ∷ tele) cl coh zero =
    subst (λ X → extend (extendTele Δ tele) T ⊢ tm-var 0 ⇒ X)
          (sym (trans (subst-extSub-wk (extSub^ (length tele) σ) T)
                      (cong (rename wk) (substS-closed (cl zero)))))
          (⇒-var zero)
  coh-extendTele {Γ = Γ} {Δ = Δ} {σ = σ} ((nm , T) ∷ tele) cl coh (suc j) =
    subst (λ X → extend (extendTele Δ tele) T ⊢ rename wk (extSub^ (length tele) σ (toℕ j)) ⇒ X)
          (trans (sym (subst-extSub-wk (extSub^ (length tele) σ) (lookup (extendTele Γ tele) j)))
                 (cong (substS (extSub (extSub^ (length tele) σ)))
                       (sym (lookup-extend (extendTele Γ tele) T j))))
          (weaken⇒ (coh-extendTele tele (λ j → cl (suc j)) coh j))

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
               (subst-spine coh (tele-closed-subst-params σ f (family-lookup-member {fs = IndEnv.families ind} p)) q))
        (subst (λ zs → Δ ⊢* zs ⇐* fam-indices f) (sym (substTerms-map σ is))
               (subst-spine coh (tele-closed-subst-indices σ f (family-lookup-member {fs = IndEnv.families ind} p)) r))
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-ctor {c = c} {args = args} {f = f} {ct = ct} p q) =
      subst (λ X → Δ ⊢ tm-ctor c (substTermsS σ args) ⇒ X)
            (sym (subst-ctor-result σ f ct {c = c} p))
            (⇒-ctor p (subst (λ zs → Δ ⊢* zs ⇐* ctor-args ct) (sym (substTerms-map σ args))
                             (subst-spine coh (tele-closed-subst-ctor σ f ct {c = c} p) q)))
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-case {s = s} {m = m′} {brs = brs} p q r covered) =
     ⇒-case (subst⇒ coh p) (subst⇒ coh q) (subst-branches coh r)
       (case-coverage-subst {brs = brs} σ covered)
   subst⇒ coh (⇒-effect_type p) = ⇒-effect_type (subst⇒ coh p)
   subst⇒ coh (⇒-effect_pure p) = ⇒-effect_pure (subst⇒ coh p)
   subst⇒ coh (⇒-conv der eq) = ⇒-conv (subst⇒ coh der) (subst-conv eq)
   subst⇒ coh (⇒-cumul der le) = ⇒-cumul (subst⇒ coh der) le
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
    -- `extendTele Γ (ctor-args ct)` is matched by `extendTele Δ (ctor-args ct)`
    -- via `coh-extendTele`; the body is substituted by
    -- `extSub^ (length (ctor-args ct)) σ`. The motive's substitution is the
    -- subtle step, discharged by `subst-branch-motive`.
   subst-branches : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {brs nm m′ σ}
          → Coherent {n} {m} Γ Δ σ
        → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
        → Δ ⊢*brs substBranchesS σ brs ⇐*ᵇ (nm , substS σ m′)
   subst-branches coh brs[] = brs[]
   subst-branches {Γ = Γ} {Δ = Δ} {σ = σ} coh
                  (brs∷ {cn = cn} {b = b} {brs = brs} {n = nm} {m = m′} {f = f} {ct = ct} fc db dbrs) =
     brs∷ fc
          (subst (λ X → extendTele Δ (ctor-args ct) ⊢ substS (extSub^ (length (ctor-args ct)) σ) b ⇐ X)
                 (subst-branch-motive (length (ctor-args ct)) σ m′ cn)
                 (subst⇐ (coh-extendTele (ctor-args ct) (λ j → teleField-closed f ct fc j) coh) db))
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

  -- Cumulativity in the declarative typing closure, NOT conversion.
  ⇒-cumul-infer : ∀ {n} {Γ : Ctx n} {t i j} → Γ ⊢ t ⇒ tm-type i → i ≤ˡ j → Γ ⊢ t ⇒ tm-type j
  ⇒-cumul-infer = ⇒-cumul

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

  -- GENERALISATION: a hole-free term that CHECKS against a type INFERS it.
  --
  -- The only checking rule that does not already give an inference is
  -- `⇐-hole`, and a hole-free term is never a hole. Every other rule
  -- (`⇐-lam`, `⇐-infer`, `⇐-conv`, `⇐-cumul`) has a matching inference rule
  -- with the SAME premises — `⇐-lam` and `⇒-lam` share theirs — so the proof
  -- is a direct structural recursion, with no `Value` side condition.
  --
  -- This is the lemma that DISSOLVES the inference-preservation gaps: the
  -- checking-mode β/ζ reducts (`preserve-β` / `preserve-ζ`) infer their
  -- type as soon as they are hole-free, which they are when the redex is
  -- final. `value-infer` is the special case at a value, but the general
  -- form needs no value structure at all.
  check-infer : ∀ {n} {Γ : Ctx n} {a A} → HoleFree a → Γ ⊢ a ⇐ A → Γ ⊢ a ⇒ A
  check-infer hf (⇐-infer der eq) = ⇒-conv der eq
  check-infer hf (⇐-conv der eq) = ⇒-conv (check-infer hf der) eq
  check-infer hf (⇐-cumul der le) = ⇒-cumul-infer der le
  check-infer hf (⇐-lam {g = g} {d = d} {b = b} {c = c} ds body) =
    ⇒-lam {g = g} {d = d} {b = b} {c = c} ds body
  check-infer hf ⇐-hole = ⊥-elim (hf _ refl)

  -- Checking cumulativity also covers a reduct that is a development
  -- hole. All other checking derivations give declarative inference;
  -- no inference rule for holes is added.
  check-infer-or-hole : ∀ {n} {Γ : Ctx n} {a A}
    → Γ ⊢ a ⇐ A → (Γ ⊢ a ⇒ A) ⊎ (∃ λ name → a ≡ tm-hole name)
  check-infer-or-hole (⇐-lam ds body) = inj₁ (⇒-lam ds body)
  check-infer-or-hole (⇐-infer der eq) = inj₁ (⇒-conv der eq)
  check-infer-or-hole (⇐-cumul der le) = inj₁ (⇒-cumul der le)
  check-infer-or-hole ⇐-hole = inj₂ (_ , refl)
  check-infer-or-hole (⇐-conv der eq) with check-infer-or-hole der
  ... | inj₁ inferred = inj₁ (⇒-conv inferred eq)
  ... | inj₂ hole = inj₂ hole

  check-cumul : ∀ {n} {Γ : Ctx n} {a i j}
    → Γ ⊢ a ⇐ tm-type i → i ≤ˡ j → Γ ⊢ a ⇐ tm-type j
  check-cumul der le with check-infer-or-hole der
  ... | inj₁ inferred = ⇐-cumul inferred le
  ... | inj₂ (name , refl) = ⇐-hole

  -- `HoleFree` is preserved by substitution: the only former that can
  -- become a hole is a variable (handled by the substitution) or a hole
  -- (excluded by the hypothesis); every other former is not a hole by
  -- constructor discrimination.
  HoleFreeSub : Sub → Set
  HoleFreeSub σ = ∀ k → HoleFree (σ k)

  substS-hole-free : ∀ (t : Term) (σ : Sub) → HoleFreeSub σ → HoleFree t → HoleFree (substS σ t)
  substS-hole-free (tm-type l) σ hfs hf name ()
  substS-hole-free (tm-var k) σ hfs hf = hfs k
  substS-hole-free (tm-pi g d c) σ hfs hf name ()
  substS-hole-free (tm-lam g d b) σ hfs hf name ()
  substS-hole-free (tm-let g ty v b) σ hfs hf name ()
  substS-hole-free (tm-app f a) σ hfs hf name ()
  substS-hole-free (tm-data n ps is) σ hfs hf name ()
  substS-hole-free (tm-ctor n args) σ hfs hf name ()
  substS-hole-free (tm-case s m brs) σ hfs hf name ()
  substS-hole-free (tm-global n) σ hfs hf name ()
  substS-hole-free (tm-int_type) σ hfs hf name ()
  substS-hole-free (tm-int_lit k) σ hfs hf name ()
  substS-hole-free (tm-nat_lit k) σ hfs hf name ()
  substS-hole-free (tm-bounded_lit k) σ hfs hf name ()
  substS-hole-free (tm-float_type) σ hfs hf name ()
  substS-hole-free (tm-float_lit) σ hfs hf name ()
  substS-hole-free (tm-binary_type) σ hfs hf name ()
  substS-hole-free (tm-atom_type) σ hfs hf name ()
  substS-hole-free (tm-atom_lit n) σ hfs hf name ()
  substS-hole-free (tm-effect_type t) σ hfs hf name ()
  substS-hole-free (tm-effect_pure t) σ hfs hf name ()
  substS-hole-free (tm-effect_bind e k) σ hfs hf name ()
  substS-hole-free (tm-hole n) σ hfs hf = ⊥-elim (hf n refl)
  substS-hole-free (tm-absurd) σ hfs hf name ()

  -- The two substitutions the β/ζ rules use are hole-free when their
  -- inputs are.
  topSub-hole-free : ∀ {a} → HoleFree a → HoleFreeSub (topSub a)
  topSub-hole-free hf zero = hf
  topSub-hole-free hf (suc k) name ()

  substTop-hole-free : ∀ {a t} → HoleFree a → HoleFree t → HoleFree (substTopT a t)
  substTop-hole-free hf hft = substS-hole-free _ (topSub _) (topSub-hole-free hf) hft

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
  lam-type-pi (⇒-cumul der le) with lam-type-pi der
  ... | c , eq , pi-der = ⊥-elim (universe-not-pi eq)

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
  ⇒-lam-inv-aux T c (⇒-cumul der le) eq = ⊥-elim (universe-not-pi eq)

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
    conv⇒ w eq (⇒-case p q r covered) = ⇒-conv (⇒-case (conv⇒ w (Conversion.≈-refl conv) p) (conv⇒ w (Conversion.≈-refl conv) q) (conv-branches w r) covered) eq
    conv⇒ w eq (⇒-effect_type p) = ⇒-conv (⇒-effect_type (conv⇒ w (Conversion.≈-refl conv) p)) eq
    conv⇒ w eq (⇒-effect_pure p) = ⇒-conv (⇒-effect_pure (conv⇒ w (Conversion.≈-refl conv) p)) eq
    conv⇒ w eq (⇒-effect_bind p q) = ⇒-conv (⇒-effect_bind (conv⇒ w (Conversion.≈-refl conv) p) (conv⇒ w (Conversion.≈-refl conv) q)) eq
    conv⇒ w eq (⇒-conv der eq′) = conv⇒ w (Conversion.≈-trans conv eq′ eq) der
    conv⇒ w eq (⇒-cumul der le) =
      ⇒-conv (⇒-cumul (conv⇒ w (Conversion.≈-refl conv) der) le) eq

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
    conv-branches {Γ = Γ} {Γ′ = Γ′} w (brs∷ {cn = cn} {b = b} {ct = ct} fc body rest) =
      brs∷ fc (conv⇐ (extTele-conv w (ctor-args ct)) (Conversion.≈-refl conv) body) (conv-branches w rest)

    -- Extend the witness under a TELESCOPE's binders (a `case` branch
    -- context). The field types are CLOSED, so they are convertible to
    -- themselves; the existing variables are `raise`-shifted.
    extTele-conv : ∀ {n} {Γ Γ′ : Ctx n} (w : ∀ i → Conversion._≈_ conv (lookup Γ i) (lookup Γ′ i))
                 → ∀ (tele : Telescope) → ∀ i
                 → Conversion._≈_ conv (lookup (extendTele Γ tele) i) (lookup (extendTele Γ′ tele) i)
    extTele-conv w [] = w
    extTele-conv w ((nm , T) ∷ tele) zero = Conversion.≈-refl conv
    extTele-conv {Γ = Γ} {Γ′ = Γ′} w ((nm , T) ∷ tele) (suc i) =
      ext-conv {Γ = extendTele Γ tele} {Γ′ = extendTele Γ′ tele} {d = T} {d′ = T}
               (Conversion.≈-refl conv) (extTele-conv {Γ = Γ} {Γ′ = Γ′} w tele) (suc i)

  -- Branch checking is stable under CONVERSION of the motive. Each branch
  -- body checks against `tm-app (rename (λ j → j + ar) m) (tm-ctor cn …)`;
  -- the motive only appears under `rename (λ j → j + ar)`, and conversion is
  -- stable under renaming (`≈-rename`), so the body's type converts.
  -- This is what lets `ξ-case-motive` be typed: the reduct's motive is only
  -- CONVERTIBLE to the redex's, not equal to it (`ReduceConv`).
  branches-conv : ∀ {n} {Γ : Ctx n} {brs nm m m′}
                → Conversion._≈_ conv m m′
                → Γ ⊢*brs brs ⇐*ᵇ (nm , m) → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
  branches-conv eq brs[] = brs[]
  branches-conv {Γ = Γ} eq (brs∷ {cn = cn} {b = b} {ct = ct} fc body rest) =
    brs∷ fc
         (⇐-conv body (Conversion.≈-app conv
                        (Conversion.≈-rename conv (λ j → j + length (ctor-args ct)) eq)
                        (Conversion.≈-refl conv)))
         (branches-conv eq rest)
  -- The `⇒-conv`-on-function case of β: `dflam` is a λ derivation whose
  -- type `T₀` converts to `tm-pi g d c`. `lam-type-pi` exposes the λ's own
  -- Π type `tm-pi g′ d′ c′`; Π injectivity gives `d′ ≈ d` and `c′ ≈ c`; the
  -- body (which checks `c′` under `d′`) is converted to check `c` under `d`
  -- by CONTEXT CONVERSION, and `substTop⇐` instantiates it.
  preserve-β-conv-aux : ∀ {n} {Γ : Ctx n} {g g′ d′ d b a c T₀}
    → Γ ⊢ tm-lam g′ d′ b ⇒ T₀
    → Conversion._≈_ conv T₀ (tm-pi g d c)
    → Γ ⊢ a ⇒ d
    → Γ ⊢ substTopT a b ⇐ substTopT a c
  preserve-β-conv-aux {Γ = Γ} {g = g} {d = d} {b = b} {a = a} {c = c} {T₀ = T₀} dflam ceq da =
    substTop⇐ {Γ = Γ} {A = d} body-checks da
    where
      c′ : Term
      c′ = proj₁ (lam-type-pi dflam)
      eq″ : Conversion._≈_ conv T₀ (tm-pi _ _ c′)
      eq″ = proj₁ (proj₂ (lam-type-pi dflam))
      der′ : Γ ⊢ tm-lam _ _ b ⇒ tm-pi _ _ c′
      der′ = proj₂ (proj₂ (lam-type-pi dflam))
      comps = conv-pi-components (Conversion.≈-trans conv (Conversion.≈-sym conv eq″) ceq)
      body-checks : extend Γ d ⊢ b ⇐ c
      body-checks = conv⇐ (ext-conv (proj₁ (proj₂ comps)) (λ i → Conversion.≈-refl conv)) (proj₂ (proj₂ comps)) (⇒-lam-inv der′)
  -- β: `(λx. b) a ⇝ b[x := a]`.
  --
  -- PROVED. `⇒-app` gives `Γ ⊢ tm-lam g d b ⇒ tm-pi g d c` (so `T =
  -- substTopT a c`) and `Γ ⊢ a ⇒ d`; `⇒-lam-inv` gives
  -- `extend Γ d ⊢ b ⇐ c`. `substTop⇐` yields
  -- `Γ ⊢ substTopT a b ⇐ substTopT a c`.
  preserve-β :
    ∀ {n} {Γ : Ctx n} {g d b a T}
    → Γ ⊢ tm-app (tm-lam g d b) a ⇒ T
    → Γ ⊢ substTopT a b ⇐ T
  preserve-β {Γ = Γ} {g = g} {d = d} {b = b} {a = a} (⇒-app {g = g} {d = d} {c = c} (⇒-lam {g = g} {d = d} {b = b} {c = c} dd db) da) =
    substTop⇐ {Γ = Γ} {A = d}
              (⇒-lam-inv {g = g} {d = d} {b = b} {c = c}
                         (⇒-lam {g = g} {d = d} {b = b} {c = c} dd db)) da
  preserve-β {Γ = Γ} {g = g} {d = d} {b = b} {a = a} (⇒-app {c = c} (⇒-conv {T = T₀} dflam ceq) da) =
    preserve-β-conv-aux dflam ceq da

  preserve-β (⇒-conv der eq) = ⇐-conv (preserve-β der) eq
  preserve-β (⇒-cumul der le) = check-cumul (preserve-β der) le



  -- ζ: `let x = v in b ⇝ b[x := v]`.
  --
  -- `⇒-let` gives `Γ ⊢ v ⇐ ty` and `extend Γ ty ⊢ b ⇒ T` (so the result
  -- type is `substTopT v T`); `check-infer` turns the checked term into an
  -- inferring one (it needs only hole-freeness, which `Final` supplies —
  -- no `Value v` side condition), and `substTop⇐` gives the result.
  preserve-ζ :
    ∀ {n} {Γ : Ctx n} {g ty v b T}
    → Γ ⊢ tm-let g ty v b ⇒ T
    → HoleFree v
    → Γ ⊢ substTopT v b ⇐ T
  preserve-ζ {Γ = Γ} {g = g} {ty = ty} {v = v} {b = b} {T = T} (⇒-let {l = l} dty dv db) hf =
    substTop⇐ {Γ = Γ} {A = ty} (⇒-check db) (check-infer hf dv)
    where
      ⇒-check : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Γ ⊢ t ⇐ T
      ⇒-check der = ⇐-infer der (Conversion.≈-refl conv)
  preserve-ζ (⇒-conv der eq) hf = ⇐-conv (preserve-ζ der hf) eq
  preserve-ζ (⇒-cumul der le) hf = check-cumul (preserve-ζ der hf) le


  ------------------------------------------------------------------------

  -- `substTopT` congruence under a convertible argument (via `≈-subst-cong`).
  ≈-substTopT-cong : ∀ {a a′ c} → Conversion._≈_ conv a a′
                   → Conversion._≈_ conv (substTopT a c) (substTopT a′ c)
  ≈-substTopT-cong {a} {a′} {c} eq =
    Conversion.≈-subst-cong conv {t = c} (λ { zero → eq ; (suc k) → Conversion.≈-refl conv })
  -- A final term is hole-free (its subterms are too).
  final-hole-free : ∀ {t} → Final t → HoleFree t
  final-hole-free ft name eq = absurd-hole (subst Final eq ft)
    where
      absurd-hole : Final (tm-hole name) → ⊥
      absurd-hole ()

  ------------------------------------------------------------------------
  -- The ι (branch substitution) and δ (certified unfolding) cases, and the
  -- `ξ-case-motive` congruence.
  --
  -- The former β/ζ inference-preservation gaps are DISSOLVED: the
  -- checking-mode `preserve-β` / `preserve-ζ` give the reduct CHECKED, and
  -- `check-infer` turns that into an INFERENCE because the redex is `Final`
  -- (hence the reduct is hole-free). Likewise `preservation⇒-case` is
  -- proved directly from the `ReduceConv` hypothesis. What remains are the
  -- ι cases (needing the `brs∷` field-telescope change), δ (needing a
  -- strengthened `Certified`), and `ξ-case-motive` (needing a
  ------------------------------------------------------------------------
  -- The ι (branch substitution) case.
  --
  -- With the branch rule typing the field binders with the constructor's
  -- argument telescope (`extendTele Γ (ctor-args ct)`), the ι reduction's
  -- substitution lemma applies directly: `argsSub args` maps the field
  -- indices to the constructor's actual arguments and the base environment
  -- back down to `Γ`.
  ------------------------------------------------------------------------

  -- Extract the branch body's typing from a `⊢*brs` derivation, given the
  -- branch's membership. The new `brs∷` stores `length (ctor-args ct)` as
  -- the branch arity, so the arity equation is `refl`.
  brs-body : ∀ {k} {Γ : Ctx k} {brs n m}
           → Γ ⊢*brs brs ⇐*ᵇ (n , m)
           → ∀ {c ar b} → (c , ar , b) ∈ brs
           → ∃ λ f → ∃ λ ct
           → findCtor c (IndEnv.families ind) ≡ just (f , ct)
             × length (ctor-args ct) ≡ ar
             × (extendTele Γ (ctor-args ct) ⊢ b
                  ⇐ tm-app (rename (λ j → j + length (ctor-args ct)) m)
                           (tm-ctor c (branch-field-vars (length (ctor-args ct)))))
  brs-body brs[] ()
  brs-body (brs∷ {ct = ct} fc db dbrs) (here refl) = _ , ct , fc , refl , db
  brs-body (brs∷ fc db dbrs) (there p) = brs-body dbrs p

  -- The `i`-th entry of a checked spine.
  spine-lookup : ∀ {k} {Γ : Ctx k} {ts tele}
               → (d : Γ ⊢* ts ⇐* tele) → (j : Fin (length ts))
               → Γ ⊢ listLookup ts j ⇐ teleField tele (cast (spine-length d) j)
  spine-lookup ⊢*[] ()
  spine-lookup (⊢*∷ {x = x} {xs = xs} dx dxs) zero = dx
  spine-lookup (⊢*∷ dx dxs) (suc j) = spine-lookup dxs j

  -- `argsSub args` maps the field indices to the constructor's arguments and
  -- the base environment back down to `Γ`. This is the coherence the ι
  -- substitution lemma consumes. Proved by induction on the telescope: a
  -- field position maps to the constructor argument (which checks the
  -- telescope entry, hence — being final — infers it via `check-infer`); a
  -- base-environment position is the identity.
  argsSub-coh : ∀ {n} {Γ : Ctx n} (tele : Telescope) (args : List Term) (k : ℕ)
              → FinalTerms args
              → (∀ j → Scoped 0 (teleField tele j))
              → (sp : Γ ⊢* args ⇐* tele)
              → Coherent (extendTele Γ tele) Γ (argsSub-go k args)
  argsSub-coh {Γ = Γ} [] [] k ft[] cl ⊢*[] j =
    subst (λ X → Γ ⊢ tm-var (toℕ j) ⇒ X)
          (sym (substS-idSub (lookup Γ j)))
          (⇒-var j)
  argsSub-coh {Γ = Γ} ((nm , T) ∷ tele) (a ∷ args) k (ft∷ fa fargs) cl (⊢*∷ {nm = nm′} da dargs) zero =
    subst (λ X → Γ ⊢ a ⇒ X) eq (check-infer (final-hole-free fa) da)
    where
      eq : T ≡ substS (argsSub-go k (a ∷ args)) (lookup (extendTele Γ ((nm , T) ∷ tele)) zero)
      eq = sym (trans (subst-rename (argsSub-go k (a ∷ args)) wk T)
                      (trans (cong (λ σ → substS σ T) (funext (λ i → refl)))
                             (substS-closed (cl zero))))
  argsSub-coh {Γ = Γ} ((nm , T) ∷ tele) (a ∷ args) k (ft∷ fa fargs) cl (⊢*∷ {nm = nm′} da dargs) (suc j) =
    subst (λ X → Γ ⊢ argsSub-go (suc k) args (toℕ j) ⇒ X) eq
          (argsSub-coh tele args (suc k) fargs (λ j → cl (suc j)) dargs j)
    where
      eq : substS (argsSub-go (suc k) args) (lookup (extendTele Γ tele) j)
         ≡ substS (argsSub-go k (a ∷ args)) (lookup (extendTele Γ ((nm , T) ∷ tele)) (suc j))
      eq = sym (trans (cong (substS (argsSub-go k (a ∷ args)))
                             (lookup-renameCtx wk (extendTele Γ tele) j))
                      (trans (subst-rename (argsSub-go k (a ∷ args)) wk (lookup (extendTele Γ tele) j))
                             (cong (λ σ → substS σ (lookup (extendTele Γ tele) j))
                                   (funext (λ i → refl)))))
  ------------------------------------------------------------------------
  -- The ι (branch substitution) case.
  --
  -- With the branch rule typing the field binders with the constructor's
  -- argument telescope (`extendTele Γ (ctor-args ct)`), the ι reduction's
  -- substitution lemma applies directly: `argsSub args` maps the field
  -- indices to the constructor's actual arguments and the base environment
  -- back down to `Γ`. The motive, weakened by `length (ctor-args ct)` into
  -- the branch context, is restored by the substitution; the constructor of
  -- field variables becomes the constructor of the actual arguments.
  ------------------------------------------------------------------------

  -- `argsSub args` undoes the `length tele`-fold weakening of the motive.
  substArgs-motive : ∀ {args} (tele : Telescope) (m : Term)
    → length args ≡ length tele
    → substS (argsSub args) (rename (shiftRen (length tele) 0) m) ≡ m
  substArgs-motive {args} tele m len =
    trans (subst-rename (argsSub args) (shiftRen (length tele) 0) m)
          (trans (cong (λ σ → substS σ m) (funext (λ i → argsSub-wk i)))
                 (substS-idSub m))
    where
      -- `argsSub args (i + length tele) ≡ tm-var i` (the base environment).
      argsSub-wk : ∀ i → (argsSub args ∘s shiftRen (length tele) 0) i ≡ tm-var i
      argsSub-wk i = trans (cong (argsSub args) (trans (+-comm i (length tele)) (cong (λ Z → Z + i) (sym len))))
                           (argsSub-go-raise 0 args i)

  -- Substituting the constructor's arguments for the branch field variables
  -- recovers the constructor applied to the arguments.
  substArgs-field-vars : ∀ {args} (tele : Telescope)
    → length args ≡ length tele
    → substTermsS (argsSub args) (branch-field-vars (length tele)) ≡ args
  substArgs-field-vars {args} tele len =
    trans (cong (substTermsS (argsSub args)) (map-tm-var-upto (length tele)))
          (trans (substTerms-map (argsSub args) (map tm-var (upto (length tele))))
                 (trans (map-compose (substS (argsSub args)) tm-var (upto (length tele)))
                        (trans (cong (λ g → map g (upto (length tele)))
                                     (funext (λ k → refl)))
                               (trans (cong (map (argsSub args)) (sym (cong upto len)))
                                      (map-argsSub-upto args)))))
    where
      map-tm-var-upto : ∀ n → branch-field-vars n ≡ map tm-var (upto n)
      map-tm-var-upto n = refl

      map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (f ∘ g) xs
      map-compose f g [] = refl
      map-compose f g (x ∷ xs) = cong₂ _∷_ refl (map-compose f g xs)

      -- `map (argsSub args) (upto (length args)) ≡ args`.
      map-argsSub-upto : ∀ (as : List Term) → map (argsSub as) (upto (length as)) ≡ as
      map-argsSub-upto [] = refl
      map-argsSub-upto (x ∷ as) =
        cong₂ _∷_ (argsSub-go-field 0 (x ∷ as) zero) (map-argsSub-upto-shift as)
        where
          -- `map (argsSub (x ∷ as)) (map suc (upto (length as))) ≡ as`.
          map-argsSub-upto-shift : ∀ as → map (argsSub (x ∷ as)) (map suc (upto (length as))) ≡ as
          map-argsSub-upto-shift as =
            trans (map-compose (argsSub (x ∷ as)) suc (upto (length as)))
                  (trans (cong (λ f → map f (upto (length as)))
                               (funext (λ i → argsSub-go-shift (x ∷ as) i)))
                         (map-argsSub-upto as))
            where
              -- `argsSub (x ∷ as) (suc i) ≡ argsSub as i`.
              argsSub-go-shift : ∀ (ys : List Term) i → argsSub (x ∷ as) (suc i) ≡ argsSub as i
              argsSub-go-shift ys i = refl

  -- The motive, weakened by `length (ctor-args ct)` into the branch context,
  -- restored by the substitution.
  substArgs-motive-ctor : ∀ {args} (ct : Ctor) (m : Term)
    → length args ≡ length (ctor-args ct)
    → substS (argsSub args) (rename (λ j → j + length (ctor-args ct)) m) ≡ m
  substArgs-motive-ctor {args} ct m len =
    substArgs-motive {args} (ctor-args ct) m len

  -- A branch's body is final when the branch list is and the branch is a
  -- member.
  finalBranches-member : ∀ {bs} → FinalBranches bs → ∀ {cn ar b}
                       → (cn , ar , b) ∈ bs → Final b
  finalBranches-member (fb∷ fb fbs) (here refl) = fb
  finalBranches-member (fb∷ fb fbs) (there p) = finalBranches-member fbs p

  -- `argsSub args` is final when `args` are.
  argsSub-final : ∀ {args} → FinalTerms args → HoleFreeSub (argsSub args)
  argsSub-final {args} ft = go 0 args ft
    where
      go : ∀ k (ys : List Term) → FinalTerms ys → HoleFreeSub (argsSub-go k ys)
      go k [] ft[] i = λ name ()
      go k (y ∷ ys) (ft∷ fy fys) zero = final-hole-free fy
      go k (y ∷ ys) (ft∷ fy fys) (suc i) = go (suc k) ys fys i

  -- Invert a `tm-ctor` inference: a constructor's inference derivation
  -- exposes its owning family, telescope, and checked argument spine.
  ctor-inv : ∀ {k} {Γ : Ctx k} {c args n ps is}
           → Γ ⊢ tm-ctor c args ⇒ tm-data n ps is
           → ∃ λ f → ∃ λ ct
           → findCtor c (IndEnv.families ind) ≡ just (f , ct)
             × (Γ ⊢* args ⇐* ctor-args ct)
  ctor-inv der with constructor-data der
  ... | f , ct , fc , owner , sp = f , ct , fc , sp

  -- ι for a `tm-ctor` scrutinee.
  preservation-ι : ∀ {n} {Γ : Ctx n} {m brs c ar b args T}
    → Final (tm-case (tm-ctor c args) m brs)
    → Γ ⊢ tm-case (tm-ctor c args) m brs ⇒ T
    → findBranch c brs ≡ just (c , ar , b)
    → length args ≡ ar
    → Γ ⊢ substArgs args b ⇒ T
  preservation-ι {Γ = Γ} {m = m} {brs = brs} {c = c} {ar = ar} {b = b} {args = args}
                 (f-case (f-ctor fargs) fm fbs)
                 (⇒-case {ps = ps} {is = is} ds dm dbrs covered) found len =
    subst (λ X → Γ ⊢ substArgs args b ⇒ X) eq
          (check-infer (substS-hole-free b (argsSub args) (argsSub-final fargs)
                                       (final-hole-free (finalBranches-member fbs (findBranch-sound c brs found))))
                      (subst⇐ (argsSub-coh (ctor-args ct) args 0 fargs (λ j → teleField-closed f ct fc j) sp) db′))
    where
      ci = ctor-inv ds
      f = proj₁ ci
      ct = proj₁ (proj₂ ci)
      fc = proj₁ (proj₂ (proj₂ ci))
      sp = proj₂ (proj₂ (proj₂ ci))
      bd = brs-body dbrs (findBranch-sound _ _ found)
      f′ = proj₁ bd
      ct′ = proj₁ (proj₂ bd)
      fc′ = proj₁ (proj₂ (proj₂ bd))
      len′ = proj₁ (proj₂ (proj₂ (proj₂ bd)))
      db = proj₂ (proj₂ (proj₂ (proj₂ bd)))
      ct-eq : ct′ ≡ ct
      ct-eq = cong proj₂ (just-inj (trans (sym fc′) fc))
      len″ : length (ctor-args ct) ≡ ar
      len″ = subst (λ Z → length (ctor-args Z) ≡ ar) ct-eq len′
      -- the branch body, re-typed at `ct`
      db′ : extendTele Γ (ctor-args ct) ⊢ b
          ⇐ tm-app (rename (λ j → j + length (ctor-args ct)) m)
                   (tm-ctor c (branch-field-vars (length (ctor-args ct))))
      db′ = subst (λ Z → extendTele Γ (ctor-args Z) ⊢ b
                     ⇐ tm-app (rename (λ j → j + length (ctor-args Z)) m)
                              (tm-ctor c (branch-field-vars (length (ctor-args Z)))))
                  ct-eq db
      eq-motive : substS (argsSub args) (rename (λ j → j + length (ctor-args ct)) m) ≡ m
      eq-motive = substArgs-motive-ctor {args = args} ct m (trans len (sym len″))
      eq-args : substS (argsSub args) (tm-ctor c (branch-field-vars (length (ctor-args ct)))) ≡ tm-ctor c args
      eq-args = cong (tm-ctor c) (substArgs-field-vars {args = args} (ctor-args ct) (trans len (sym len″)))
      eq : substS (argsSub args)
                   (tm-app (rename (λ j → j + length (ctor-args ct)) m)
                           (tm-ctor c (branch-field-vars (length (ctor-args ct)))))
         ≡ tm-app m (tm-ctor c args)
      eq = trans (cong₂ tm-app eq-motive eq-args) refl
  preservation-ι ft (⇒-conv der eq) found len =
    ⇒-conv (preservation-ι ft der found len) eq
  preservation-ι ft (⇒-cumul der le) found len =
    ⇒-cumul (preservation-ι ft der found len) le

  -- ι for a compact `tm-nat_lit 0` scrutinee (peeled to `Z`).
  preservation-ι-nat-zero : ∀ {n} {Γ : Ctx n} {m brs ar b T}
    → Final (tm-case (tm-nat_lit 0) m brs)
    → Γ ⊢ tm-case (tm-nat_lit 0) m brs ⇒ T
    → findBranch "Z" brs ≡ just ("Z" , ar , b)
    → Γ ⊢ substArgs [] b ⇒ T
  preservation-ι-nat-zero {Γ = Γ} {m = m} {brs = brs} {b = b} {T = tm-app m (tm-nat_lit 0)}
                          (f-case f-nat_lit fm fbs)
                          (⇒-case {s = tm-nat_lit 0} {ps = ps} {is = is} ds dm dbrs covered) found =
    ⇒-conv (check-infer (subst (λ X → HoleFree X) (sym (substS-idSub b))
                                      (final-hole-free (finalBranches-member fbs (findBranch-sound "Z" brs found))))
                         db″)
           (Conversion.≈-app conv (Conversion.≈-refl conv) (Conversion.≈-nat-zero conv))
    where
      bd = brs-body dbrs (findBranch-sound "Z" brs found)
      f = proj₁ bd
      ct = proj₁ (proj₂ bd)
      fc = proj₁ (proj₂ (proj₂ bd))
      db = proj₂ (proj₂ (proj₂ (proj₂ bd)))
      args0 : ctor-args ct ≡ []
      args0 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ bc)))))) fc
      db′ : extendTele Γ [] ⊢ b ⇐ tm-app m (tm-ctor "Z" [])
      db′ = subst (λ X → extendTele Γ [] ⊢ b ⇐ X)
                  (cong₂ tm-app (rename-zero m) refl)
                  (subst (λ Z → extendTele Γ Z ⊢ b
                                 ⇐ tm-app (rename (λ j → j + length Z) m)
                                          (tm-ctor "Z" (branch-field-vars (length Z))))
                         args0 db)
        where
          rename-zero : ∀ t → rename (λ j → j + 0) t ≡ t
          rename-zero t = trans (cong (λ ρ → rename ρ t)
                                       (funext-ren (λ j → +-identityʳ j)))
                                (rename-id t)
      db″ : extendTele Γ [] ⊢ substArgs [] b ⇐ tm-app m (tm-ctor "Z" [])
      db″ = subst (λ X → extendTele Γ [] ⊢ X ⇐ tm-app m (tm-ctor "Z" []))
                   (sym (substS-idSub b)) db′
  preservation-ι-nat-zero (f-case f-nat_lit fm fbs) (⇒-conv der eq) found =
    ⇒-conv (preservation-ι-nat-zero (f-case f-nat_lit fm fbs) der found) eq
  preservation-ι-nat-zero ft (⇒-cumul der le) found =
    ⇒-cumul (preservation-ι-nat-zero ft der found) le

  -- The coherence for a single `Nat` field (the `S` / `First` cases).
  argsSub-coh-single : ∀ {n} {Γ : Ctx n} {N a}
    → IndEnv.builtins ind "nat" ≡ just N
    → Γ ⊢ a ⇒ tm-data N [] []
    → Coherent (extendTele Γ (("_" , tm-data N [] []) ∷ [])) Γ (argsSub (a ∷ []))
  -- `argsSub (a ∷ []) ∘ wk` is the identity substitution.
  argsSub-single-wk : ∀ a i → (argsSub (a ∷ []) ∘s wk) i ≡ tm-var i
  argsSub-single-wk a i = refl

  argsSub-coh-single {n = n} {Γ = Γ} {N = N} {a = a} p da zero =
    subst (λ X → Γ ⊢ a ⇒ X) eq da
    where
      eq : tm-data N [] [] ≡ substS (argsSub (a ∷ [])) (lookup (extendTele Γ (("_" , tm-data N [] []) ∷ [])) zero)
      eq = sym (trans (cong (substS (argsSub (a ∷ [])))
                             (lookup-head {n = n} Γ (tm-data N [] [])))
                      (trans (subst-rename (argsSub (a ∷ [])) wk (tm-data N [] []))
                             (trans (cong (λ σ → substS σ (tm-data N [] []))
                                          (funext (λ i → argsSub-single-wk a i)))
                                    (substS-idSub (tm-data N [] [])))))
  argsSub-coh-single {Γ = Γ} {N = N} {a = a} p da (suc i) =
    subst (λ X → Γ ⊢ tm-var (toℕ i) ⇒ X) eq (⇒-var i)
    where
      eq : lookup Γ i ≡ substS (argsSub (a ∷ [])) (lookup (extendTele Γ (("_" , tm-data N [] []) ∷ [])) (suc i))
      eq = sym (trans (cong (substS (argsSub (a ∷ [])))
                             (lookup-extend Γ (tm-data N [] []) i))
                      (trans (subst-rename (argsSub (a ∷ [])) wk (lookup Γ i))
                             (trans (cong (λ σ → substS σ (lookup Γ i))
                                          (funext (λ j → argsSub-single-wk a j)))
                                    (substS-idSub (lookup Γ i)))))

  -- ι for a compact `tm-nat_lit (suc k)` scrutinee (peeled to `S`).

  -- Invert a `tm-nat_lit` inference: it exposes the builtin `Nat` family.
  nat-lit-inv : ∀ {k} {Γ : Ctx k} {m N ps is}
              → Γ ⊢ tm-nat_lit m ⇒ tm-data N ps is
              → IndEnv.builtins ind "nat" ≡ just N
  nat-lit-inv = nat-data-family

  -- ι for a compact `tm-nat_lit (suc k)` scrutinee (peeled to `S`).
  preservation-ι-nat-suc : ∀ {n} {Γ : Ctx n} {m brs ar b k T}
    → Final (tm-case (tm-nat_lit (suc k)) m brs)
    → Γ ⊢ tm-case (tm-nat_lit (suc k)) m brs ⇒ T
    → findBranch "S" brs ≡ just ("S" , ar , b)
    → Γ ⊢ substArgs (tm-nat_lit k ∷ []) b ⇒ T
  preservation-ι-nat-suc {Γ = Γ} {m = m} {brs = brs} {b = b} {k = k} {T = tm-app m (tm-nat_lit (suc k))}
                        (f-case f-nat_lit fm fbs)
                        (⇒-case {s = tm-nat_lit (suc k)} {n = N} {ps = ps} {is = is} ds dm dbrs covered) found =
    ⇒-conv (check-infer hf (subst (λ X → Γ ⊢ substS (argsSub (tm-nat_lit k ∷ [])) b ⇐ X) eq
                                       (subst⇐ (argsSub-coh-single p (⇒-nat_lit p)) db′)))
           (Conversion.≈-app conv (Conversion.≈-refl conv) (Conversion.≈-nat-suc conv))
    where
      p : IndEnv.builtins ind "nat" ≡ just N
      p = nat-lit-inv ds
      bd = brs-body dbrs (findBranch-sound "S" brs found)
      f = proj₁ bd
      ct = proj₁ (proj₂ bd)
      fc = proj₁ (proj₂ (proj₂ bd))
      db = proj₂ (proj₂ (proj₂ (proj₂ bd)))
      argsS : ctor-args ct ≡ ("_" , tm-data N [] []) ∷ []
      argsS = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ bc))))))) p fc
      db′ : extendTele Γ (("_" , tm-data N [] []) ∷ []) ⊢ b
          ⇐ tm-app (rename (λ j → j + 1) m) (tm-ctor "S" (branch-field-vars 1))
      db′ = subst (λ Z → extendTele Γ Z ⊢ b
                     ⇐ tm-app (rename (λ j → j + length Z) m)
                              (tm-ctor "S" (branch-field-vars (length Z))))
                  argsS db
      hf : HoleFree (substS (argsSub (tm-nat_lit k ∷ [])) b)
      hf = substS-hole-free b (argsSub (tm-nat_lit k ∷ []))
             (λ { zero → final-hole-free f-nat_lit ; (suc i) → λ name () })
             (final-hole-free (finalBranches-member fbs (findBranch-sound "S" brs found)))
      eq : substS (argsSub (tm-nat_lit k ∷ []))
                   (tm-app (rename (λ j → j + 1) m) (tm-ctor "S" (branch-field-vars 1)))
         ≡ tm-app m (tm-ctor "S" (tm-nat_lit k ∷ []))
      eq = trans (cong₂ tm-app
                        (substArgs-motive (("_" , tm-data N [] []) ∷ []) m refl)
                        (cong (tm-ctor "S") (substTerms-map (argsSub (tm-nat_lit k ∷ [])) (branch-field-vars 1))))
                 refl
  preservation-ι-nat-suc (f-case f-nat_lit fm fbs) (⇒-conv der eqc) found =
    ⇒-conv (preservation-ι-nat-suc (f-case f-nat_lit fm fbs) der found) eqc
  preservation-ι-nat-suc ft (⇒-cumul der le) found =
    ⇒-cumul (preservation-ι-nat-suc ft der found) le

  -- Invert a `tm-bounded_lit` inference: it exposes the builtin `Bounded` family.
  bounded-lit-inv : ∀ {k} {Γ : Ctx k} {m B ps is}
                  → Γ ⊢ tm-bounded_lit m ⇒ tm-data B ps is
                  → IndEnv.builtins ind "bounded" ≡ just B
  bounded-lit-inv = bounded-data-family

  -- ι for a compact `tm-bounded_lit 0` scrutinee (peeled to `First`).
  preservation-ι-bounded-zero : ∀ {n} {Γ : Ctx n} {m brs ar b T}
    → Final (tm-case (tm-bounded_lit 0) m brs)
    → Γ ⊢ tm-case (tm-bounded_lit 0) m brs ⇒ T
    → findBranch "First" brs ≡ just ("First" , ar , b)
    → Γ ⊢ substArgs (tm-nat_lit 0 ∷ []) b ⇒ T
  preservation-ι-bounded-zero {Γ = Γ} {m = m} {brs = brs} {b = b}
                              {T = tm-app m (tm-bounded_lit 0)}
                              (f-case f-bounded_lit fm fbs)
                              (⇒-case {s = tm-bounded_lit 0} {n = B} {ps = ps} {is = is} ds dm dbrs covered) found =
    ⇒-conv (check-infer hf (subst (λ X → Γ ⊢ substS (argsSub (tm-nat_lit 0 ∷ [])) b ⇐ X) eq
                                       (subst⇐ (argsSub-coh-single p (⇒-nat_lit p)) db′)))
           (Conversion.≈-app conv (Conversion.≈-refl conv) (Conversion.≈-bounded-zero conv))
    where
      N = proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ bc)))))
      p : IndEnv.builtins ind "nat" ≡ just N
      p = proj₂ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ bc)))))
      bd = brs-body dbrs (findBranch-sound "First" brs found)
      f = proj₁ bd
      ct = proj₁ (proj₂ bd)
      fc = proj₁ (proj₂ (proj₂ bd))
      db = proj₂ (proj₂ (proj₂ (proj₂ bd)))
      argsF : ctor-args ct ≡ ("_" , tm-data N [] []) ∷ []
      argsF = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ bc)))))))) p fc
      db′ : extendTele Γ (("_" , tm-data N [] []) ∷ []) ⊢ b
          ⇐ tm-app (rename (λ j → j + 1) m) (tm-ctor "First" (branch-field-vars 1))
      db′ = subst (λ Z → extendTele Γ Z ⊢ b
                     ⇐ tm-app (rename (λ j → j + length Z) m)
                              (tm-ctor "First" (branch-field-vars (length Z))))
                  argsF db
      hf : HoleFree (substS (argsSub (tm-nat_lit 0 ∷ [])) b)
      hf = substS-hole-free b (argsSub (tm-nat_lit 0 ∷ []))
             (λ { zero → final-hole-free f-nat_lit ; (suc i) → λ name () })
             (final-hole-free (finalBranches-member fbs (findBranch-sound "First" brs found)))
      eq : substS (argsSub (tm-nat_lit 0 ∷ []))
                   (tm-app (rename (λ j → j + 1) m) (tm-ctor "First" (branch-field-vars 1)))
         ≡ tm-app m (tm-ctor "First" (tm-nat_lit 0 ∷ []))
      eq = trans (cong₂ tm-app
                        (substArgs-motive (("_" , tm-data N [] []) ∷ []) m refl)
                        (cong (tm-ctor "First") (substTerms-map (argsSub (tm-nat_lit 0 ∷ [])) (branch-field-vars 1))))
                 refl
  preservation-ι-bounded-zero (f-case f-bounded_lit fm fbs) (⇒-conv der eqc) found =
    ⇒-conv (preservation-ι-bounded-zero (f-case f-bounded_lit fm fbs) der found) eqc
  preservation-ι-bounded-zero ft (⇒-cumul der le) found =
    ⇒-cumul (preservation-ι-bounded-zero ft der found) le

  argsSub-double-wk : ∀ a c i → (argsSub (a ∷ c ∷ []) ∘s shiftRen 2 0) i ≡ tm-var i
  argsSub-double-wk a c i =
    subst (λ Z → argsSub-go 0 (a ∷ c ∷ []) Z ≡ tm-var i)
          (sym (+-comm i 2))
          (argsSub-go-raise 0 (a ∷ c ∷ []) i)

  -- The coherence for two fields `Nat`, `Bounded` (the `Next` case).
  argsSub-coh-double : ∀ {n} {Γ : Ctx n} {N B a c}
    → IndEnv.builtins ind "nat" ≡ just N
    → IndEnv.builtins ind "bounded" ≡ just B
    → Γ ⊢ a ⇒ tm-data N [] []
    → Γ ⊢ c ⇒ tm-data B [] []
    → Coherent (extendTele Γ (("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ []))
               Γ (argsSub (a ∷ c ∷ []))
  argsSub-coh-double {n = n} {Γ = Γ} {N = N} {B = B} {a = a} {c = c} p q da dc zero =
    subst (λ X → Γ ⊢ a ⇒ X) eq da
    where
      eq : tm-data N [] [] ≡ substS (argsSub (a ∷ c ∷ []))
             (lookup (extendTele Γ (("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ [])) zero)
      eq = sym (trans (cong (substS (argsSub (a ∷ c ∷ [])))
                             (lookup-head {n = suc n} (extend Γ (tm-data B [] [])) (tm-data N [] [])))
                      (substS-closed {σ = argsSub (a ∷ c ∷ [])} {t = tm-data N [] []} (sc-data {d = 0} (st[] {d = 0}) (st[] {d = 0}))))
  argsSub-coh-double {n = n} {Γ = Γ} {N = N} {B = B} {a = a} {c = c} p q da dc (suc zero) =
    subst (λ X → Γ ⊢ c ⇒ X) eq dc
    where
      eq : tm-data B [] [] ≡ substS (argsSub (a ∷ c ∷ []))
             (lookup (extendTele Γ (("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ [])) (suc zero))
      eq = sym (trans (cong (substS (argsSub (a ∷ c ∷ [])))
                             (lookup-head {n = n} Γ (tm-data B [] [])))
                      (substS-closed {σ = argsSub (a ∷ c ∷ [])} {t = tm-data B [] []} (sc-data {d = 0} (st[] {d = 0}) (st[] {d = 0}))))
  argsSub-coh-double {Γ = Γ} {N = N} {B = B} {a = a} {c = c} p q da dc (suc (suc i)) =
    subst (λ X → Γ ⊢ tm-var (toℕ i) ⇒ X) eq (⇒-var i)
    where
      eq : lookup Γ i ≡ substS (argsSub (a ∷ c ∷ []))
             (lookup (extendTele Γ (("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ [])) (suc (suc i)))
      eq = sym (trans (cong (substS (argsSub (a ∷ c ∷ [])))
                             (trans (lookup-extend (extend Γ (tm-data B [] [])) (tm-data N [] []) (suc i))
                                    (cong (rename wk) (lookup-extend Γ (tm-data B [] []) i))))
                      (trans (subst-rename (argsSub (a ∷ c ∷ [])) wk (rename wk (lookup Γ i)))
                             (trans (cong (λ σ → substS σ (rename wk (lookup Γ i)))
                                          (funext (λ j → refl)))
                                    (trans (subst-rename (argsSub (a ∷ c ∷ []) ∘s wk) wk (lookup Γ i))
                                           (trans (cong (λ σ → substS σ (lookup Γ i)) (funext (λ j → argsSub-double-wk2 j)))
                                                  (substS-idSub (lookup Γ i)))))))
        where
          argsSub-double-wk2 : ∀ j → ((argsSub (a ∷ c ∷ []) ∘s wk) ∘s wk) j ≡ tm-var j
          argsSub-double-wk2 j = refl

  -- ι for a compact `tm-bounded_lit (suc k)` scrutinee (peeled to `Next`).
  preservation-ι-bounded-suc : ∀ {n} {Γ : Ctx n} {m brs ar b k T}
    → Final (tm-case (tm-bounded_lit (suc k)) m brs)
    → Γ ⊢ tm-case (tm-bounded_lit (suc k)) m brs ⇒ T
    → findBranch "Next" brs ≡ just ("Next" , ar , b)
    → Γ ⊢ substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b ⇒ T
  preservation-ι-bounded-suc {Γ = Γ} {m = m} {brs = brs} {b = b} {k = k}
                             {T = tm-app m (tm-bounded_lit (suc k))}
                             (f-case f-bounded_lit fm fbs)
                             (⇒-case {s = tm-bounded_lit (suc k)} {n = B} {ps = ps} {is = is} ds dm dbrs covered) found =
    ⇒-conv (check-infer hf (subst (λ X → Γ ⊢ substS (argsSub (tm-nat_lit k ∷ tm-bounded_lit k ∷ [])) b ⇐ X) eq
                                       (subst⇐ (argsSub-coh-double p q (⇒-nat_lit p) (⇒-bounded_lit q)) db′)))
           (Conversion.≈-app conv (Conversion.≈-refl conv) (Conversion.≈-bounded-suc conv))
    where
      N = proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ bc)))))
      p : IndEnv.builtins ind "nat" ≡ just N
      p = proj₂ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ bc)))))
      q : IndEnv.builtins ind "bounded" ≡ just B
      q = bounded-lit-inv ds
      bd = brs-body dbrs (findBranch-sound "Next" brs found)
      f = proj₁ bd
      ct = proj₁ (proj₂ bd)
      fc = proj₁ (proj₂ (proj₂ bd))
      db = proj₂ (proj₂ (proj₂ (proj₂ bd)))
      argsN : ctor-args ct ≡ ("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ []
      argsN = (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ bc))))))))) p q fc
      db′ : extendTele Γ (("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ []) ⊢ b
          ⇐ tm-app (rename (λ j → j + 2) m) (tm-ctor "Next" (branch-field-vars 2))
      db′ = subst (λ Z → extendTele Γ Z ⊢ b
                     ⇐ tm-app (rename (λ j → j + length Z) m)
                              (tm-ctor "Next" (branch-field-vars (length Z))))
                  argsN db
      hf : HoleFree (substS (argsSub (tm-nat_lit k ∷ tm-bounded_lit k ∷ [])) b)
      hf = substS-hole-free b (argsSub (tm-nat_lit k ∷ tm-bounded_lit k ∷ []))
             (λ { zero → final-hole-free f-nat_lit
                ; (suc zero) → final-hole-free f-bounded_lit
                ; (suc (suc i)) → λ name () })
             (final-hole-free (finalBranches-member fbs (findBranch-sound "Next" brs found)))
      eq : substS (argsSub (tm-nat_lit k ∷ tm-bounded_lit k ∷ []))
                   (tm-app (rename (λ j → j + 2) m) (tm-ctor "Next" (branch-field-vars 2)))
         ≡ tm-app m (tm-ctor "Next" (tm-nat_lit k ∷ tm-bounded_lit k ∷ []))
      eq = trans (cong₂ tm-app
                        (substArgs-motive (("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ []) m refl)
                        (cong (tm-ctor "Next") (substTerms-map (argsSub (tm-nat_lit k ∷ tm-bounded_lit k ∷ [])) (branch-field-vars 2))))
                 refl
  preservation-ι-bounded-suc (f-case f-bounded_lit fm fbs) (⇒-conv der eqc) found =
    ⇒-conv (preservation-ι-bounded-suc (f-case f-bounded_lit fm fbs) der found) eqc
  preservation-ι-bounded-suc ft (⇒-cumul der le) found =
    ⇒-cumul (preservation-ι-bounded-suc ft der found) le
  -- Head and tail of a non-empty `FinalTerms` (local copies; the ones in
  -- Proof.FinalPreservation are not exported into this module).
  ft-head : ∀ {x xs} → FinalTerms (x ∷ xs) → Final x
  ft-head (ft∷ fx fxs) = fx

  ft-tail : ∀ {x xs} → FinalTerms (x ∷ xs) → FinalTerms xs
  ft-tail (ft∷ fx fxs) = fxs

  mutual
    -- Spine preservation under an element update: a checked spine stays
    -- checked when the element at position `i` steps (every other entry is
    -- unchanged).
    preservation-spine : ∀ {n} {Γ : Ctx n} {ts} {tele : Telescope}
                         (i : Fin (len ts)) {x′}
                       → FinalTerms ts
                       → Γ ⊢* ts ⇐* tele
                       → _⇝_ sig (lookupAt ts i) x′
                       → Γ ⊢* setAt ts i x′ ⇐* tele
    preservation-spine zero (ft∷ fx fxs) (⊢*∷ dx dxs) step =
      ⊢*∷ (preservation fx dx step) dxs
    preservation-spine (suc i) (ft∷ fx fxs) (⊢*∷ dx dxs) step =
      ⊢*∷ dx (preservation-spine i fxs dxs step)

    -- A checked branch list stays checked when its bodies reduce.
    preservation-brs : ∀ {n} {Γ : Ctx n} {brs brs′ nm m}
                     → FinalBranches brs
                     → Γ ⊢*brs brs ⇐*ᵇ (nm , m)
                     → _⇝*ᵇ_ sig brs brs′
                     → Γ ⊢*brs brs′ ⇐*ᵇ (nm , m)
    preservation-brs fb[] brs[] ⇝ᵇ-nil = brs[]
    preservation-brs (fb∷ fb fbs) (brs∷ fc body rest) (⇝ᵇ-cons steps steps′) =
      brs∷ fc (preservation-star fb body steps) (preservation-brs fbs rest steps′)

    preservation-star : ∀ {n} {Γ : Ctx n} {b b′ T}
                      → Final b → Γ ⊢ b ⇐ T → _⇝*_ sig b b′ → Γ ⊢ b′ ⇐ T
    preservation-star fb db ⇝*-refl = db
    preservation-star fb db (⇝*-step s ss) = preservation-star (final-preservation sig cert fb s) (preservation fb db s) ss

    preservation⇒ :
      ∀ {n} {Γ : Ctx n} {t t′ T}
      → Final t
      → Γ ⊢ t ⇒ T
      → _⇝_ sig t t′
      → Γ ⊢ t′ ⇒ T
    preservation⇒ ft (⇒-conv der eq) rw = ⇒-conv (preservation⇒ ft der rw) eq
    preservation⇒ ft (⇒-cumul der le) rw = ⇒-cumul (preservation⇒ ft der rw) le
    -- β: the checking-mode `preserve-β` gives the reduct CHECKED; the redex
    -- is final, so the reduct is hole-free and INFERS its type (`check-infer`).
    preservation⇒ (f-app (f-lam fd fb) fa) (⇒-app df da) β =
      check-infer (substTop-hole-free (final-hole-free fa) (final-hole-free fb))
                  (preserve-β (⇒-app df da))
    -- ζ: likewise, via `preserve-ζ`.
    preservation⇒ (f-let fty fv fb) (⇒-let {g = g} {ty = ty} {v = v} {b = b} {T = T} dty dv db) ζ =
      check-infer (substTop-hole-free (final-hole-free fv) (final-hole-free fb))
                  (preserve-ζ (⇒-let {g = g} {ty = ty} {v = v} {b = b} {T = T} dty dv db)
                              (final-hole-free fv))
    preservation⇒ (f-app ff fa) (⇒-app df da) (ξ-app₁ step) =
      ⇒-app (preservation⇒ ff df step) da
    preservation⇒ {Γ = Γ} (f-app ff fa) (⇒-app {a = a} {c = c} df da) (ξ-app₂ {a′ = a′} step) =
      ⇒-conv (⇒-app df (preservation⇒ fa da step))
              (Conversion.≈-sym conv (≈-substTopT-cong {c = c} (rc step)))
    preservation⇒ {Γ = Γ} (f-let fty fv fb) (⇒-let {v = v} {T = T} dty dv db) (ξ-let {v′ = v′} step) =
      ⇒-conv (⇒-let dty (preservation fv dv step) db)
              (Conversion.≈-sym conv (≈-substTopT-cong {c = T} (rc step)))
    -- ξ-let-ty: only the declared type reduces; the result type is unchanged.
    -- The value was checked against `ty`; it checks against `ty′` by conversion
    -- (`rc` gives `⇝ ⊆ ≈`), and the body is transported across the context
    -- conversion `extend Γ ty ≈ extend Γ ty′`.
    preservation⇒ (f-let fty fv fb) (⇒-let dty dv db) (ξ-let-ty step) =
      ⇒-let (preservation⇒ fty dty step) (⇐-conv dv (rc step))
            (conv⇒ (ext-conv (rc step) (λ i → Conversion.≈-refl conv)) (Conversion.≈-refl conv) db)
    -- ξ-let-body: the body reduces under the extended context; the result type
    -- is unchanged (it substitutes the value, which does not move). The reduct
    -- is final (`final-preservation`), hence hole-free, so `check-infer`
    -- recovers the inference the `⇒-let` rule needs.
    preservation⇒ (f-let fty fv fb) (⇒-let dty dv db) (ξ-let-body step) =
      ⇒-let dty dv
            (check-infer (final-hole-free (final-preservation sig cert fb step))
                         (preservation fb (⇐-infer db (Conversion.≈-refl conv)) step))
    preservation⇒ (f-case fs fm fbs) (⇒-case ds dm dbrs covered) (ξ-case step) =
      ⇒-conv (⇒-case (preservation⇒ fs ds step) dm dbrs covered)
              (Conversion.≈-app conv (Conversion.≈-refl conv)
                                    (Conversion.≈-sym conv (rc step)))
    preservation⇒ (f-case fs fm fbs) (⇒-case ds dm dbrs covered) (ξ-case-brs steps) =
      ⇒-case ds dm (preservation-brs fbs dbrs steps) (case-coverage-reduce sig steps covered)
    preservation⇒ (f-case fs fm fbs) (⇒-case ds dm dbrs covered) (ξ-case-motive step) =
      ⇒-conv (⇒-case ds (preservation⇒ fm dm step)
                       (branches-conv (rc step) dbrs) covered)
              (Conversion.≈-app conv (Conversion.≈-sym conv (rc step))
                                    (Conversion.≈-refl conv))
    preservation⇒ {Γ = Γ} (f-pi fd fc) (⇒-pi {d = d} dd dc) (ξ-pi-dom {d′ = d′} step) =
      ⇒-pi (preservation⇒ fd dd step)
           (conv⇒ (ext-conv (rc step) (λ i → Conversion.≈-refl conv)) (Conversion.≈-refl conv) dc)
    preservation⇒ (f-pi fd fc) (⇒-pi dd dc) (ξ-pi-cod step) =
      ⇒-pi dd (preservation⇒ fc dc step)
    preservation⇒ {Γ = Γ} (f-lam fd fb) (⇒-lam {d = d} dd db) (ξ-lam-dom {d′ = d′} step) =
      ⇒-conv (⇒-lam (preservation⇒ fd dd step)
                     (conv⇐ (ext-conv (rc step) (λ i → Conversion.≈-refl conv)) (Conversion.≈-refl conv) db))
              (Conversion.≈-sym conv (Conversion.≈-pi conv (rc step) (Conversion.≈-refl conv)))
    preservation⇒ (f-lam fd fb) (⇒-lam dd db) (ξ-lam-body step) =
      ⇒-lam dd (preservation fb db step)
    preservation⇒ (f-data fps fis) (⇒-data p q r) (ξ-data-params-at i step) =
      ⇒-data p (preservation-spine i fps q step) r
    preservation⇒ (f-data fps fis) (⇒-data p q r) (ξ-data-indices-at i step) =
      ⇒-data p q (preservation-spine i fis r step)
    preservation⇒ (f-ctor fargs) (⇒-ctor p q) (ξ-ctor-at i step) =
      ⇒-ctor p (preservation-spine i fargs q step)
    preservation⇒ (f-effect_type ft) (⇒-effect_type p) (ξ-effect_type step) =
      ⇒-effect_type (preservation⇒ ft p step)
    preservation⇒ (f-effect_pure ft) (⇒-effect_pure p) (ξ-effect_pure step) =
      ⇒-effect_pure (preservation⇒ ft p step)
    preservation⇒ (f-effect_bind fe fk) (⇒-effect_bind p q) (ξ-effect_bind₁ step) =
      ⇒-effect_bind (preservation⇒ fe p step) q
    preservation⇒ (f-effect_bind fe fk) (⇒-effect_bind p q) (ξ-effect_bind₂ step) =
      ⇒-effect_bind p (preservation⇒ fk q step)
    preservation⇒ ft der (ι found len) = preservation-ι ft der found len
    preservation⇒ ft der (ι-nat-zero found refl) = preservation-ι-nat-zero ft der found
    preservation⇒ ft der (ι-nat-suc found refl) = preservation-ι-nat-suc ft der found
    preservation⇒ ft der (ι-bounded-zero found refl) = preservation-ι-bounded-zero ft der found
    preservation⇒ ft der (ι-bounded-suc found refl) = preservation-ι-bounded-suc ft der found
    preservation⇒ ft (⇒-global {f = f} {T = T} p) (δ {body′ = body′} q) =
      weaken-closed (proj₁ (ctyped q p)) (proj₁ closed f p) (proj₂ (ctyped q p))

    preservation :
      ∀ {n} {Γ : Ctx n} {t t′ T}
      → Final t
      → Γ ⊢ t ⇐ T
      → _⇝_ sig t t′
      → Γ ⊢ t′ ⇐ T
    preservation ft (⇐-infer der eq) rw = ⇐-infer (preservation⇒ ft der rw) eq
    preservation ft (⇐-conv der eq) rw = ⇐-conv (preservation ft der rw) eq
    preservation ft (⇐-cumul der le) rw = ⇐-cumul (preservation⇒ ft der rw) le
    -- A checked λ reduces only under its domain or its body (`ξ-lam-dom` /
    -- `ξ-lam-body`); every other rule's head is a different former, so the
    -- `rw` pattern-match is exhaustive.
    preservation (f-lam fd fb) (⇐-lam {g = g} {d = d} {b = b} {c = c} {l = l} ds body) (ξ-lam-dom {d′ = d′} step) =
      ⇐-conv (⇐-lam (preservation⇒ fd ds step)
                     (conv⇐ (ext-conv (rc step) (λ i → Conversion.≈-refl conv))
                            (Conversion.≈-refl conv) body))
              (Conversion.≈-sym conv (Conversion.≈-pi conv (rc step) (Conversion.≈-refl conv)))
    preservation (f-lam fd fb) (⇐-lam ds body) (ξ-lam-body step) =
      ⇐-lam ds (preservation fb body step)
    -- A hole has no reduction rule, so `rw` is impossible.
    preservation () (⇐-hole) rw