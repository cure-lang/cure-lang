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
open import Core.Signature using (Telescope)
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; lookup-extend;
                                lookup-renameCtx;
                                extendⁿ; extendTele; teleField; fieldFin)
open import Proof.Substitution using (shift-0; rename-closed; shiftRen-k0)
open import Data.List using (List; []; _∷_; length; reverse; map)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_,_; proj₂)

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

------------------------------------------------------------------------
-- The telescope extension `extendTele`.
--
-- `extendTele Γ tele` binds the telescope's entries, the FIRST entry
-- INNERMOST (`Γ ▷ A_ar ▷ … ▷ A₁`). Its two lookup laws are the workhorses
-- of the `case` branch cases of the renaming and substitution lemmas:
--
--   * a FIELD position (index `i < length tele`) holds the `i`-th
--     telescope entry, which is CLOSED;
--   * an EXISTING variable, lifted by `_↑ʳ_` (as `length tele ↑ʳ j`),
--     holds `lookup Γ j` renamed by the `length tele`-fold weakening
--     `shiftRen (length tele) 0`.
------------------------------------------------------------------------

-- A field position holds the corresponding telescope entry, provided the
-- telescope is CLOSED (so `extend`'s `wk`-renaming is the identity).
lookup-extendTele-field : ∀ {m} (Γ : Ctx m) (tele : Telescope) (i : Fin (length tele))
  → (∀ j → Scoped 0 (teleField tele j))
  → lookup (extendTele Γ tele) (fieldFin tele i) ≡ teleField tele i
lookup-extendTele-field Γ [] ()
lookup-extendTele-field Γ ((nm , T) ∷ tele) zero cl = rename-closed (cl zero)
lookup-extendTele-field Γ ((nm , T) ∷ tele) (suc i) cl =
  trans (lookup-renameCtx wk (extendTele Γ tele) (fieldFin tele i))
        (trans (cong (rename wk) (lookup-extendTele-field Γ tele i (λ j → cl (suc j))))
               (rename-closed (cl (suc i))))

-- An existing variable, lifted by `_↑ʳ_`, is found with its type renamed
-- by `shiftRen (length tele) 0` (the `length tele`-fold weakening).
lookup-extendTele-raise : ∀ {m} (Γ : Ctx m) (tele : Telescope) (j : Fin m)
  → lookup (extendTele Γ tele) (length tele ↑ʳ j)
  ≡ rename (shiftRen (length tele) 0) (lookup Γ j)
lookup-extendTele-raise Γ [] j = sym (shift-0 0 (lookup Γ j))
lookup-extendTele-raise Γ ((nm , T) ∷ tele) j =
  trans (lookup-extend (extendTele Γ tele) T (length tele ↑ʳ j))
        (trans (cong (rename wk) (lookup-extendTele-raise Γ tele j))
               (trans (rename-compose wk (shiftRen (length tele) 0) (lookup Γ j))
                      (cong (λ ρ → rename ρ (lookup Γ j))
                            (funext-ren (λ k → sym (+-suc k (length tele)))))))

------------------------------------------------------------------------
-- The branch context morphism for a TELESCOPE extension.
--
-- `extF-tele tele idx` extends a morphism `idx : Fin n → Fin m` to the
-- field binders: a field position maps to itself (`_↑ˡ_`), an existing
-- variable is lifted by `length tele ↑ʳ_`. It is the `Fin` analogue of the
-- renaming-level `ext^ (length tele)`.
------------------------------------------------------------------------

extF-tele : ∀ {n m} (tele : Telescope) → (Fin n → Fin m)
          → Fin (length tele + n) → Fin (length tele + m)
extF-tele [] idx i = idx i
extF-tele ((nm , T) ∷ tele) idx zero = zero
extF-tele ((nm , T) ∷ tele) idx (suc j) = suc (extF-tele tele idx j)

-- The morphism realises the renaming `ext^ (length tele) ρ`.
extF-tele-coh : ∀ {n m} (tele : Telescope) (ρ : Ren) (idx : Fin n → Fin m)
  → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
  → ∀ (j : Fin (length tele + n))
  → toℕ (extF-tele tele idx j) ≡ ext^ (length tele) ρ (toℕ j)
extF-tele-coh [] ρ idx coh j = coh j
extF-tele-coh ((nm , T) ∷ tele) ρ idx coh zero = refl
extF-tele-coh ((nm , T) ∷ tele) ρ idx coh (suc j) = cong suc (extF-tele-coh tele ρ idx coh j)

-- The lookup law: the morphism transports the branch context lookup, with
-- the type renamed by `ext^ (length tele) ρ`. The FIELD positions hold
-- CLOSED telescope entries (so the renaming is the identity there); the
-- EXISTING variables use the raise law.
lookup-extF-tele : ∀ {n m} (Γ : Ctx n) (Δ : Ctx m) (tele : Telescope)
                   (ρ : Ren) (idx : Fin n → Fin m)
  → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
  → (∀ j → Scoped 0 (teleField tele j))
  → ∀ (j : Fin (length tele + n))
  → lookup (extendTele Δ tele) (extF-tele tele idx j)
  ≡ rename (ext^ (length tele) ρ) (lookup (extendTele Γ tele) j)
lookup-extF-tele Γ Δ [] ρ idx law cl j = law j
lookup-extF-tele Γ Δ ((nm , T) ∷ tele) ρ idx law cl zero =
  sym (trans (rename-compose (ext^ (suc (length tele)) ρ) wk T)
             (trans (cong (λ ρ′ → rename ρ′ T)
                          (funext-ren (λ k → ext^-wk (length tele) ρ k)))
                    (trans (sym (rename-compose wk (ext^ (length tele) ρ) T))
                           (cong (rename wk) (rename-closed {ρ = ext^ (length tele) ρ} (cl zero))))))
  where
    -- `ext^ (suc n) ρ (suc k) ≡ suc (ext^ n ρ k)`, i.e., the extension
    -- commutes with `wk`.
    ext^-wk : ∀ n (ρ : Ren) k → ext^ (suc n) ρ (suc k) ≡ (wk ∘ ext^ n ρ) k
    ext^-wk n ρ k = refl
lookup-extF-tele Γ Δ ((nm , T) ∷ tele) ρ idx law cl (suc j) =
  trans (lookup-extend (extendTele Δ tele) T (extF-tele tele idx j))
        (trans (cong (rename wk) (lookup-extF-tele Γ Δ tele ρ idx law (λ k → cl (suc k)) j))
               (trans (ext-wk-rename (ext^ (length tele) ρ) (lookup (extendTele Γ tele) j))
                      (cong (rename (ext^ (suc (length tele)) ρ))
                            (sym (lookup-extend (extendTele Γ tele) T j)))))
