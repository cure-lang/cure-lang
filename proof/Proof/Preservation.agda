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
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax
open import Core.Signature using (IndEnv; Family; Ctor; Telescope; findFamily; findCtor;
                                   fam-params; fam-indices; fam-level; fam-name;
                                   ctor-args; ctor-params; ctor-indices)
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; lookup-extend; lookup-renameCtx; Conversion)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Substitution
open import Proof.Context using (lookup-weaken; lookup-head)

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

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

  -- A global's declared type is closed, so renaming leaves it unchanged.
  postulate
    rename-global-type : ∀ (ρ : Ren) (f : Name) (T : Term)
      → Signature.type-of sig f ≡ just T → rename ρ T ≡ T

  -- Helper obligations for the spine/branch cases of renaming.
  postulate
    ren-app : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {f a g d c ρ} (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ a ⇐ d
      → Δ ⊢ rename ρ (tm-app f a) ⇒ rename ρ (substT 0 a c)
    ren-data : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {nm ps is f ρ} (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → findFamily nm (IndEnv.families ind) ≡ just f
      → Γ ⊢* ps ⇐* fam-params f → Γ ⊢* is ⇐* fam-indices f
      → Δ ⊢ rename ρ (tm-data nm ps is) ⇒ rename ρ (tm-type (fam-level f))
    ren-ctor : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {c args f ct ρ} (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      → Γ ⊢* args ⇐* ctor-args ct
      → Δ ⊢ rename ρ (tm-ctor c args) ⇒ rename ρ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
    ren-case : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {s m′ brs nm ps is T ρ} (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → Γ ⊢ s ⇒ tm-data nm ps is → Γ ⊢ m′ ⇒ T → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
      → Δ ⊢ rename ρ (tm-case s m′ brs) ⇒ rename ρ (tm-app m′ s)
    ren-let : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {g ty v b l T ρ} (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → Γ ⊢ ty ⇒ tm-type l → Γ ⊢ v ⇐ ty → extend Γ ty ⊢ b ⇒ T
      → Δ ⊢ rename ρ (tm-let g ty v b) ⇒ rename ρ (substTopT v T)
    ren-effect-bind : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {e k A B ρ} (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → Γ ⊢ e ⇒ tm-effect_type A → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type B)
      → Δ ⊢ rename ρ (tm-effect_bind e k) ⇒ rename ρ (tm-effect_type B)

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
    ⇒-lam (ren⇒ idx coh law dd) (ren⇒ (ext-idx idx) (ext-coh ρ idx coh) (ext-law d idx law) db)
  ren⇒ idx coh law (⇒-app df da) = ren-app idx coh law df da
  ren⇒ {Γ = Γ} {Δ = Δ} {ρ = ρ} idx coh law (⇒-let {ty = ty} dty dv db) =
    ren-let idx coh law dty dv db
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
  ren⇒ idx coh law (⇒-data p q r) = ren-data idx coh law p q r
  ren⇒ idx coh law (⇒-ctor p q) = ren-ctor idx coh law p q
  ren⇒ idx coh law (⇒-case p q r) = ren-case idx coh law p q r
  ren⇒ idx coh law (⇒-effect_type p) = ⇒-effect_type (ren⇒ idx coh law p)
  ren⇒ idx coh law (⇒-effect_pure p) = ⇒-effect_pure (ren⇒ idx coh law p)
  ren⇒ idx coh law (⇒-effect_bind p q) = ren-effect-bind idx coh law p q

  -- Weakening is the instance of the fundamental lemma at `wk`.
  weaken⇒ : ∀ {n} {Γ : Ctx n} {t T S} → Γ ⊢ t ⇒ T → extend Γ S ⊢ rename wk t ⇒ rename wk T
  weaken⇒ {n} {Γ} {S = S} der = ren⇒ (suc {n}) (λ i → refl) (λ i → lookup-extend Γ S i) der

  postulate
    weaken⇐ : ∀ {n} {Γ : Ctx n} {t T S} → Γ ⊢ t ⇐ T → extend Γ S ⊢ rename wk t ⇐ rename wk T

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
  -- OPEN OBLIGATION: the index-0 case is `subst-extSub-wk`; the index-suc
  -- case is weakening of the original coherence.
  postulate
    coh-extend :
      ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ d}
      → Coherent {n} {m} Γ Δ σ
      → Coherent (extend Γ d) (extend Δ (substS σ d)) (extSub σ)

  -- The length of a context, exposed for the metatheory.
  lengthCtx : ∀ {n} → Ctx n → ℕ
  lengthCtx {n} _ = n

  ------------------------------------------------------------------------
  -- The substitution lemma.
  ------------------------------------------------------------------------

  -- Helper obligations for the spine/branch cases and conversion.
  postulate
    subst-app : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {f a g d c σ}
      → Coherent {n} {m} Γ Δ σ
      → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ a ⇐ d
      → Δ ⊢ substS σ (tm-app f a) ⇒ substS σ (substT 0 a c)
    subst-data : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {nm ps is f σ}
      → Coherent {n} {m} Γ Δ σ
      → findFamily nm (IndEnv.families ind) ≡ just f
      → Γ ⊢* ps ⇐* fam-params f → Γ ⊢* is ⇐* fam-indices f
      → Δ ⊢ substS σ (tm-data nm ps is) ⇒ substS σ (tm-type (fam-level f))
    subst-ctor : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {c args f ct σ}
      → Coherent {n} {m} Γ Δ σ
      → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      → Γ ⊢* args ⇐* ctor-args ct
      → Δ ⊢ substS σ (tm-ctor c args) ⇒ substS σ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
    subst-case : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {s m′ brs nm ps is T σ}
      → Coherent {n} {m} Γ Δ σ
      → Γ ⊢ s ⇒ tm-data nm ps is → Γ ⊢ m′ ⇒ T → Γ ⊢*brs brs ⇐*ᵇ (nm , m′)
      → Δ ⊢ substS σ (tm-case s m′ brs) ⇒ substS σ (tm-app m′ s)
    subst-conv : ∀ {t u σ}
      → Conversion._≈_ conv t u
      → Conversion._≈_ conv (substS σ t) (substS σ u)
    subst-global : ∀ {m} {Δ : Ctx m} {f} (T : Term) (σ : Sub)
      → Signature.type-of sig f ≡ just T
      → Δ ⊢ tm-global f ⇒ substS σ T
    subst-effect-bind : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {e k A B σ}
      → Coherent {n} {m} Γ Δ σ
      → Γ ⊢ e ⇒ tm-effect_type A
      → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type B)
      → Δ ⊢ substS σ (tm-effect_bind e k) ⇒ substS σ (tm-effect_type B)

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
     ⇒-lam (subst⇒ coh dd) (subst⇒ (coh-extend {Γ = Γ} {Δ = Δ} coh) db)
   subst⇒ coh (⇒-app df da) = subst-app coh df da
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
   subst⇒ coh (⇒-data p q r) = subst-data coh p q r
   subst⇒ coh (⇒-ctor p q) = subst-ctor coh p q
   subst⇒ coh (⇒-case p q r) = subst-case coh p q r
   subst⇒ coh (⇒-effect_type p) = ⇒-effect_type (subst⇒ coh p)
   subst⇒ coh (⇒-effect_pure p) = ⇒-effect_pure (subst⇒ coh p)
   subst⇒ coh (⇒-effect_bind p q) = subst-effect-bind coh p q

   subst⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {t T σ}
          → Coherent {n} {m} Γ Δ σ
          → Γ ⊢ t ⇐ T
          → Δ ⊢ substS σ t ⇐ substS σ T
   subst⇐ {Γ = Γ} {Δ = Δ} {σ = σ} coh (⇐-lam {g = g} {d = d} {b = b} {g′ = g′} {d′ = d′} {c = c} eq conv-eq body) =
    ⇐-lam {g = g} {d = substS σ d} {b = substS (extSub σ) b}
          {g′ = g′} {d′ = substS σ d′} {c = substS (extSub σ) c}
          eq
          (subst-conv conv-eq)
          (subst⇐ {Γ = extend Γ d′} {Δ = extend Δ (substS σ d′)} (coh-extend {Γ = Γ} {Δ = Δ} coh) body)
   subst⇐ coh (⇐-hole) = ⇐-hole
   subst⇐ coh (⇐-infer der eq) = ⇐-infer (subst⇒ coh der) (subst-conv eq)
   subst⇐ coh (⇐-cumul der le) = ⇐-cumul (subst⇒ coh der) le

  ------------------------------------------------------------------------
  -- The top-level substitution (for β and ζ).
  ------------------------------------------------------------------------

  -- Substitution at the top of a term (using `topSub` from Core.Syntax).
  substTop : Term → Term → Term
  substTop a t = substS (topSub a) t

  postulate
    substTop⇒ :
      ∀ {n} {Γ : Ctx n} {t T A a}
      → extend Γ A ⊢ t ⇒ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substTop a t ⇒ substTop a T

  postulate
    substTop⇐ :
      ∀ {n} {Γ : Ctx n} {t T A a}
      → extend Γ A ⊢ t ⇐ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substTop a t ⇐ substTop a T

  ------------------------------------------------------------------------
  -- Preservation
  ------------------------------------------------------------------------

  postulate
    preservation :
      ∀ {t t′ T}
      → ⟨⟩ ⊢ t ⇒ T
      → _⇝_ sig t t′
      → ⟨⟩ ⊢ t′ ⇒ T
