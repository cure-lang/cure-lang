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
-- with the well-formedness condition on the context that makes the
-- `⇒-var` cases go through, and proved by induction on the derivation.
--
-- STATUS: the substitution lemma and the four preservation cases are the
-- current research frontier. Each is marked `postulate` with a strategy.
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
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin; Conversion)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Substitution
open import Proof.Context using (lookup-weaken; lookup-head; toℕ-wkFin)

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  ------------------------------------------------------------------------
  -- Well-formedness of a context.
  --
  -- The type at index `k` is scoped in the prefix below it. This is the
  -- standard well-formed-context condition, and it is exactly what makes
  -- the `⇒-var` cases of the substitution lemma go through: substituting a
  -- variable leaves the types of the OTHER variables unchanged.
  ------------------------------------------------------------------------

  WfCtx : Context → Set
  WfCtx ⟨⟩ = ⊤
  WfCtx (Γ ▷ T) = WfCtx Γ × Scoped (lengthCtx Γ) T

  ------------------------------------------------------------------------
  -- Substitution.
  --
  -- The general substitution lemma. Given a substitution `σ` and a target
  -- context `Δ` with the coherence
  --
  --     coh : ∀ k → Δ ⊢ σ k ⇐ substS σ (lookup Γ k)
  --
  -- then `Γ ⊢ t ⇐ T` implies `Δ ⊢ substS σ t ⇐ substS σ T`.
  --
  -- The binder case extends the coherence to `extSub σ` at the context
  -- `extend Δ (substS σ d)`, using `subst-extSub-wk` and weakening.
  ------------------------------------------------------------------------

  -- The coherence condition: every substituted term infers the substituted
  -- type of the variable it replaces.
  Coherent : Context → Context → Sub → Set
  Coherent Γ Δ σ = ∀ (k : Fin (lengthCtx Γ)) → Δ ⊢ σ (toℕ k) ⇒ substS σ (lookup Γ k)

  ------------------------------------------------------------------------
  -- Weakening (needed for the extended coherence).
  --
  -- OPEN OBLIGATION: the binder cases need `rename (ext wk)` threaded
  -- through the body. The lookup law is proved; the term-level induction is
  -- the remaining piece.
  ------------------------------------------------------------------------

  postulate
    weaken⇒ : ∀ {Γ t T S} → Γ ⊢ t ⇒ T → extend Γ S ⊢ rename wk t ⇒ rename wk T

  postulate
    weaken⇐ : ∀ {Γ t T S} → Γ ⊢ t ⇐ T → extend Γ S ⊢ rename wk t ⇐ rename wk T

  ------------------------------------------------------------------------
  -- The extended coherence for the binder case.
  ------------------------------------------------------------------------

  -- `extend Δ (substS σ d) ⊢ extSub σ (toℕ k) ⇒ substS (extSub σ) (lookup (extend Γ d) k)`.
  -- The index-0 case is `subst-extSub-wk`; the index-suc case is weakening
  -- of the original coherence.
  postulate
    coh-extend :
      ∀ {Γ Δ σ d}
      → Coherent Γ Δ σ
      → Coherent (extend Γ d) (extend Δ (substS σ d)) (extSub σ)

  ------------------------------------------------------------------------
  -- The substitution lemma.
  ------------------------------------------------------------------------

  -- Helper obligations for the spine/branch cases and conversion.
  postulate
    subst-app : ∀ {Γ Δ f a g d c σ}
      → Coherent Γ Δ σ
      → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ a ⇐ d
      → Δ ⊢ substS σ (tm-app f a) ⇒ substS σ (substT 0 a c)
    subst-data : ∀ {Γ Δ n ps is f σ}
      → Coherent Γ Δ σ
      → findFamily n (IndEnv.families ind) ≡ just f
      → Γ ⊢* ps ⇐* fam-params f → Γ ⊢* is ⇐* fam-indices f
      → Δ ⊢ substS σ (tm-data n ps is) ⇒ substS σ (tm-type (fam-level f))
    subst-ctor : ∀ {Γ Δ c args f ct σ}
      → Coherent Γ Δ σ
      → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      → Γ ⊢* args ⇐* ctor-args ct
      → Δ ⊢ substS σ (tm-ctor c args) ⇒ substS σ (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
    subst-case : ∀ {Γ Δ s m brs n ps is T σ}
      → Coherent Γ Δ σ
      → Γ ⊢ s ⇒ tm-data n ps is → Γ ⊢ m ⇒ T → Γ ⊢*brs brs ⇐*ᵇ (n , m)
      → Δ ⊢ substS σ (tm-case s m brs) ⇒ substS σ (tm-app m s)
    subst-effect-bind : ∀ {Γ Δ e k A B σ}
      → Coherent Γ Δ σ
      → Γ ⊢ e ⇒ tm-effect_type A
      → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type B)
      → Δ ⊢ substS σ (tm-effect_bind e k) ⇒ substS σ (tm-effect_type B)
    subst-global : ∀ {Δ f} (T : Term) (σ : Sub)
      → Signature.type-of sig f ≡ just T
      → Δ ⊢ tm-global f ⇒ substS σ T
    subst-conv : ∀ {Γ Δ t u σ}
      → Coherent Γ Δ σ
      → Conversion._≈_ conv t u
      → Conversion._≈_ conv (substS σ t) (substS σ u)
    ren-conv-eq : ∀ {Γ Δ d d′ σ}
      → Coherent Γ Δ σ
      → Conversion._≈_ conv d d′
      → Conversion._≈_ conv (substS σ d) (substS σ d′)

  mutual
   subst⇒ : ∀ {Γ Δ t T σ}
          → Coherent Γ Δ σ
          → Γ ⊢ t ⇒ T
          → Δ ⊢ substS σ t ⇒ substS σ T
   subst⇒ coh (⇒-type p) = ⇒-type p
   subst⇒ coh (⇒-var i) = coh i
   subst⇒ coh (⇒-pi dd dc) = ⇒-pi (subst⇒ coh dd) (subst⇒ (coh-extend coh) dc)
   subst⇒ coh (⇒-lam dd db) = ⇒-lam (subst⇒ coh dd) (subst⇒ (coh-extend coh) db)
   subst⇒ coh (⇒-app df da) = subst-app coh df da
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-let {g = g} {ty = ty} {v = v} {b = b} {l = l} {T = T} dty dv db) =
    subst (λ X → Δ ⊢ tm-let g (substS σ ty) (substS σ v) (substS (extSub σ) b) ⇒ X)
          (sym (subst-topSub σ v T))
          (⇒-let (subst⇒ coh dty) (subst⇐ coh dv) (subst⇒ (coh-extend coh) db))
   subst⇒ {Δ = Δ} {σ = σ} coh (⇒-global {f = f} {T = T} p) = subst-global {Δ = Δ} T σ p
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

   subst⇐ : ∀ {Γ Δ t T σ}
         → Coherent Γ Δ σ
         → Γ ⊢ t ⇐ T
         → Δ ⊢ substS σ t ⇐ substS σ T
   subst⇐ {σ = σ} coh (⇐-lam {g = g} {d = d} {b = b} {g′ = g′} {d′ = d′} {c = c} eq conv-eq body) =
    ⇐-lam {g = g} {d = substS σ d} {b = substS (extSub σ) b}
          {g′ = g′} {d′ = substS σ d′} {c = substS (extSub σ) c}
          eq
          (ren-conv-eq coh conv-eq)
          (subst⇐ (coh-extend coh) body)
   subst⇐ coh (⇐-hole) = ⇐-hole
   subst⇐ coh (⇐-infer der eq) = ⇐-infer (subst⇒ coh der) (subst-conv coh eq)
   subst⇐ coh (⇐-cumul der le) = ⇐-cumul (subst⇒ coh der) le

  ------------------------------------------------------------------------
  -- The top-level substitution (for β and ζ).
  ------------------------------------------------------------------------

  -- Substitution at the top of a term (using `topSub` from
  -- Proof/Substitution).
  substTop : Term → Term → Term
  substTop a t = substS (topSub a) t

  postulate
    substTop⇒ :
      ∀ {Γ t T A a}
      → extend Γ A ⊢ t ⇒ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substTop a t ⇒ substTop a T

  postulate
    substTop⇐ :
      ∀ {Γ t T A a}
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
