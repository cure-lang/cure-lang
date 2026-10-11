------------------------------------------------------------------------
-- Context lemmas.
--
-- The weakening and substitution lemmas (Proof/Preservation.agda) need
-- algebraic facts about the typing context. With the LENGTH-INDEXED context
-- of Core.Typing, lookup is a total function on `Fin n` and `extend` is
-- definitional, so the de Bruijn bookkeeping reduces to `refl`-level
-- identities.
--
-- STATUS: all lemmas in this module are PROVED.
------------------------------------------------------------------------
module Proof.Context where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ; _↑ʳ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Function using (_∘_)

open import Core.Syntax
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; lookup-extend;
                                extendⁿ)
open import Proof.Substitution using (shift-0)

------------------------------------------------------------------------
-- Weakening a lookup.
--
-- Extending a context with a fresh binder shifts every existing variable
-- up by one, with its type renamed by `wk`. Definitional with the
-- length-indexed context (`lookup-extend` from Core.Typing).
------------------------------------------------------------------------

lookup-weaken : ∀ {n} (Γ : Ctx n) (T : Term) (i : Fin n)
              → lookup (extend Γ T) (suc i) ≡ rename wk (lookup Γ i)
lookup-weaken = lookup-extend

------------------------------------------------------------------------
-- The head variable.
--
-- Looking up index 0 in an extended context gives the renamed fresh binder.
------------------------------------------------------------------------

lookup-head : ∀ {n} (Γ : Ctx n) (T : Term) → lookup (extend Γ T) zero ≡ rename wk T
lookup-head Γ T = refl

------------------------------------------------------------------------
-- The multi-binder extension `extendⁿ`.
--
-- `extendⁿ Γ k` prepends `k` fresh `tm-hole "field"` binders (the branch
-- fields). Its two lookup laws are the workhorses of the `case` branch
-- cases of the renaming and substitution lemmas:
--
--   * a FIELD position (index `< k`) holds a hole;
--   * an EXISTING variable `j`, lifted by `_↑ʳ_` (as `k ↑ʳ j`), holds `lookup Γ j`
--     renamed by the `k`-fold weakening `shiftRen k 0`.
--
-- Because `extendⁿ` is indexed by `k + n` (cast-free), both laws are
-- clean inductions on `k`.
------------------------------------------------------------------------

-- The head position of `extendⁿ Γ (suc k)` is a field hole.
lookup-extendⁿ-zero : ∀ {n} (Γ : Ctx n) (k : ℕ)
                    → lookup (extendⁿ Γ (suc k)) zero ≡ tm-hole "field"
lookup-extendⁿ-zero Γ k = refl

-- An existing variable, lifted by `_↑ʳ_`, is found with its type
-- renamed by `shiftRen k 0` (the `k`-fold weakening).
lookup-extendⁿ-raise : ∀ {n} (Γ : Ctx n) (k : ℕ) (j : Fin n)
                     → lookup (extendⁿ Γ k) (k ↑ʳ j)
                     ≡ rename (shiftRen k 0) (lookup Γ j)
lookup-extendⁿ-raise Γ zero j = lookup-extendⁿ-raise-base Γ j
  where
    -- `shiftRen 0 0` is pointwise `_+ 0`, so renaming by it is the identity
    -- (`shift-0` at cutoff 0). This is the only place `shift-0` is needed.
    lookup-extendⁿ-raise-base : ∀ {n} (Γ : Ctx n) (j : Fin n)
      → lookup Γ j ≡ rename (shiftRen 0 0) (lookup Γ j)
    lookup-extendⁿ-raise-base Γ j = sym (shift-0 0 (lookup Γ j))
lookup-extendⁿ-raise Γ (suc k) j =
  trans (lookup-extend (extendⁿ Γ k) (tm-hole "field") (k ↑ʳ j))
        (trans (cong (rename wk) (lookup-extendⁿ-raise Γ k j))
               (trans (rename-compose wk (shiftRen k 0) (lookup Γ j))
                      (cong (λ ρ → rename ρ (lookup Γ j)) (funext-ren (wk-shiftRen k)))))
  where
    -- `wk ∘ shiftRen k 0 ≡ shiftRen (suc k) 0`, pointwise.
    wk-shiftRen : ∀ k j → (wk ∘ shiftRen k 0) j ≡ shiftRen (suc k) 0 j
    wk-shiftRen k j = sym (+-suc j k)

------------------------------------------------------------------------
-- The branch context morphism.
--
-- The `case` branch cases must transport a branch body from
-- `extendⁿ Γ ar` to `extendⁿ Δ ar`, where `Δ` is related to `Γ` by a
-- morphism `idx : Fin n → Fin m`. The morphism extends to the field
-- binders by `extF`: field positions map to themselves, existing
-- variables are lifted by `_↑ʳ_`.
--
-- `extF k idx` is the `Fin`-level `k`-fold extension of `idx`; it is the
-- `Fin` analogue of the renaming-level `ext^` (which acts on `ℕ → ℕ`).
------------------------------------------------------------------------

extF : ∀ {n m} (k : ℕ) → (Fin n → Fin m) → Fin (k + n) → Fin (k + m)
extF zero idx j = idx j
extF (suc k) idx zero = zero
extF (suc k) idx (suc j) = suc (extF k idx j)

-- The extended morphism realises the extended renaming `ext^ k ρ`.
extF-coh : ∀ {n m} (k : ℕ) (ρ : Ren) (idx : Fin n → Fin m)
         → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
         → ∀ (j : Fin (k + n)) → toℕ (extF k idx j) ≡ ext^ k ρ (toℕ j)
extF-coh zero ρ idx coh j = coh j
extF-coh (suc k) ρ idx coh zero = refl
extF-coh (suc k) ρ idx coh (suc j) = cong suc (extF-coh k ρ idx coh j)

-- The extended lookup law: the morphism transports the branch context
-- lookup, with the type renamed by `ext^ k ρ`. This is the law the
-- `case` branch case of the renaming lemma consumes.
lookup-extF : ∀ {n m} (Γ : Ctx n) (Δ : Ctx m) (k : ℕ) (ρ : Ren) (idx : Fin n → Fin m)
  → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
  → ∀ (j : Fin (k + n))
  → lookup (extendⁿ Δ k) (extF k idx j) ≡ rename (ext^ k ρ) (lookup (extendⁿ Γ k) j)
lookup-extF Γ Δ zero ρ idx law j = law j
lookup-extF Γ Δ (suc k) ρ idx law zero = refl
lookup-extF Γ Δ (suc k) ρ idx law (suc j) =
  trans (lookup-extend (extendⁿ Δ k) (tm-hole "field") (extF k idx j))
        (trans (cong (rename wk) (lookup-extF Γ Δ k ρ idx law j))
               (trans (ext-wk-rename (ext^ k ρ) (lookup (extendⁿ Γ k) j))
                      (cong (rename (ext^ (suc k) ρ))
                            (sym (lookup-extend (extendⁿ Γ k) (tm-hole "field") j)))))
