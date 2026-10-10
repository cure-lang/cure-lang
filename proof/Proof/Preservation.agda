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
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
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
open import Core.Signature
open import Core.Reduction
open import Core.Typing using (Context; _∋_; here; there; extend; Conversion)
open import Proof.Values using (Canonical; Neutral; Value)
open import Proof.Substitution

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion) where

  open Core.Typing.Typing ind sig conv

  ------------------------------------------------------------------------
  -- The substitution lemma.
  --
  -- If `Γ , x : A ⊢ b : B` and `Γ ⊢ a : A`, then `Γ ⊢ b[x := a] : B[x := a]`.
  --
  -- Stated for the inference judgment. The checking judgment follows by
  -- `⇐-infer` / `⇐-lam` (with the domain shift).
  --
  -- Proof strategy: induction on the derivation of `Γ , x : A ⊢ b : B`.
  --   * `⇒-var here`     — the substituted variable is the one we replace,
  --                        so `b[x := a] = a` and `B[x := a] = A`;
  --   * `⇒-var (there p)`— the variable is untouched; use weakening;
  --   * `⇒-lam`/`⇒-pi`   — descend under the binder, shifting `a` by 1;
  --   * `⇒-app`/`⇒-case` — recompose after the IH.
  -- The shift/subst laws (Proof/Substitution.agda) discharge the de Bruijn
  -- bookkeeping.
  ------------------------------------------------------------------------

  -- Weakening: extending the context does not change typability.
  --
  -- If `Γ ⊢ t ⇒ T` then `Γ , S ⊢ t ⇒ T` (with the appropriate shift).
  --
  -- OPEN OBLIGATION: proved by induction on the derivation; every rule is
  -- stable under context extension up to `shift 1 0`.
  postulate
    weaken⇒ :
      ∀ {Γ t T S}
      → Γ ⊢ t ⇒ T
      → (S ∷ Γ) ⊢ shift 1 0 t ⇒ shift 1 0 T

  -- Substitution into the inference judgment.
  --
  -- OPEN OBLIGATION: the heart of β/ζ Preservation. Proved by induction on
  -- the derivation, as described above.
  postulate
    subst⇒ :
      ∀ {Γ t T A a}
      → (A ∷ Γ) ⊢ t ⇒ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇒ substT 0 a T

  -- Substitution into the checking judgment.
  postulate
    subst⇐ :
      ∀ {Γ t T A a}
      → (A ∷ Γ) ⊢ t ⇐ T
      → Γ ⊢ a ⇐ A
      → Γ ⊢ substT 0 a t ⇐ substT 0 a T

  ------------------------------------------------------------------------
  -- Preservation
  ------------------------------------------------------------------------

  -- Preservation: if `· ⊢ e : T` and `e ⇝ e′`, then `· ⊢ e′ : T`.
  --
  -- Proof strategy: induction on the reduction derivation.
  --   * β  — `(λx.b) a ⇝ b[x := a]`: the λ was checked against a Π
  --          `Π(x:A).B`, so `b` checks against `B` under `x:A`; apply
  --          `subst⇐` to get `b[x:=a]` at `B[x:=a]`, which is the type of
  --          the application;
  --   * ζ  — `let x = v in b ⇝ b[x := v]`: identical to β;
  --   * ι  — `case (ctor c args) ⇝ b_c[args]`: the branch was checked
  --          against the motive at `c`'s indices; the scrutinee's indices
  --          are those same indices (branch_unify solved the equation), so
  --          the result type is preserved;
  --   * δ  — `global f ⇝ body(f)`: `Certified` guarantees `body(f)` was
  --          checked against `f`'s declared type; the step is
  --          type-preserving by `check_def`'s conclusion;
  --   * ξ-* — congruence: apply the IH to the reduced subterm.
  --
  -- OPEN OBLIGATION: the induction. The β/ζ cases consume `subst⇐`; the δ
  -- case consumes the `Certified` side condition (threaded by the caller).
  postulate
    preservation :
      ∀ {t t′ T}
      → [] ⊢ t ⇒ T
      → _⇝_ sig t t′
      → [] ⊢ t′ ⇒ T
