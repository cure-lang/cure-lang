------------------------------------------------------------------------
-- Conversion-parametric native syntax inversions. Bodies are checked but
-- opaque to consumers: no unfolding of a concrete reduction model while
-- elaborating inversion proofs. Not substitution or preservation.
------------------------------------------------------------------------
module Proof.DependentTypingInversion where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Grade using (unrestricted)
open import Core.Universe using (Level; l0; l2)
open import Core.Signature
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.DependentTyping
open import Core.Reduction using (Signature)

module Laws (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.DependentTyping.Typing ind sig conv
  open Conversion

  abstract
    eq : (t : Term) → _≈_ conv t t
    eq t = ≈-refl conv {t = t}
    compose : ∀ a b c → _≈_ conv a b → _≈_ conv b c → _≈_ conv a c
    compose a b c = ≈-trans conv {t = a} {u = b} {v = c}

    pi-not-sort : ∀ {g d c l} → _≈_ conv (tm-pi g d c) (tm-type l) → ⊥
    pi-not-sort {g} {d} {c} {l} equal
      with ≈-heads conv {t = tm-pi g d c} {u = tm-type l} ty-pi ty-universe equal
    ... | ()
    sort-not-pi : ∀ {g d c l} → _≈_ conv (tm-type l) (tm-pi g d c) → ⊥
    sort-not-pi {g} {d} {c} {l} equal
      with ≈-heads conv {t = tm-type l} {u = tm-pi g d c} ty-universe ty-pi equal
    ... | ()
    atom-not-sort : ∀ {l} → _≈_ conv tm-atom_type (tm-type l) → ⊥
    atom-not-sort {l} equal
      with ≈-heads conv {t = tm-atom_type} {u = tm-type l} ty-atom ty-universe equal
    ... | ()
    float-not-sort : ∀ {l} → _≈_ conv tm-float_type (tm-type l) → ⊥
    float-not-sort {l} equal
      with ≈-heads conv {t = tm-float_type} {u = tm-type l} ty-float ty-universe equal
    ... | ()

    atom-inference : ∀ {n} {Γ : Ctx n} {name A}
      → Γ ⊢ tm-atom_lit name ⇒ A → _≈_ conv tm-atom_type A
    atom-inference ⇒-atom_lit = eq tm-atom_type
    atom-inference {A = A} (⇒-conv {T = B} der equal) =
      compose tm-atom_type B A (atom-inference der) equal
    atom-inference (⇒-cumul der le) = ⊥-elim (atom-not-sort (atom-inference der))
    atom-checking : ∀ {n} {Γ : Ctx n} {name A}
      → Γ ⊢ tm-atom_lit name ⇐ A → _≈_ conv tm-atom_type A
    atom-checking {A = A} (⇐-infer {T′ = B} der equal) =
      compose tm-atom_type B A (atom-inference der) equal
    atom-checking {A = A} (⇐-conv {T = B} der equal) =
      compose tm-atom_type B A (atom-checking der) equal
    atom-checking (⇐-cumul der le) = ⊥-elim (atom-not-sort (atom-inference der))
    float-inference : ∀ {n} {Γ : Ctx n} {A}
      → Γ ⊢ tm-float_lit ⇒ A → _≈_ conv tm-float_type A
    float-inference ⇒-float_lit = eq tm-float_type
    float-inference {A = A} (⇒-conv {T = B} der equal) =
      compose tm-float_type B A (float-inference der) equal
    float-inference (⇒-cumul der le) = ⊥-elim (float-not-sort (float-inference der))
    float-checking : ∀ {n} {Γ : Ctx n} {A}
      → Γ ⊢ tm-float_lit ⇐ A → _≈_ conv tm-float_type A
    float-checking {A = A} (⇐-infer {T′ = B} der equal) =
      compose tm-float_type B A (float-inference der) equal
    float-checking {A = A} (⇐-conv {T = B} der equal) =
      compose tm-float_type B A (float-checking der) equal
    float-checking (⇐-cumul der le) = ⊥-elim (float-not-sort (float-inference der))

    -- Native syntax inversions preserve arbitrary conversion intermediates.
    lambda-inference : ∀ {n} {Γ : Ctx n} {g d b A}
      → Γ ⊢ tm-lam g d b ⇒ A
      → ∃ λ c → (extend Γ d ⊢ b ⇐ c) × _≈_ conv (tm-pi g d c) A
    lambda-inference {g = g} {d = d} (⇒-lam {c = c} kind checked) =
      c , checked , eq (tm-pi g d c)
    lambda-inference {g = g} {d = d} {A = A} (⇒-conv {T = B} der equal)
      with lambda-inference der
    ... | c , checked , between = c , checked , compose (tm-pi g d c) B A between equal
    lambda-inference (⇒-cumul der le) with lambda-inference der
    ... | c , checked , between = ⊥-elim (pi-not-sort between)
    lambda-checking : ∀ {n} {Γ : Ctx n} {g d b A}
      → Γ ⊢ tm-lam g d b ⇐ A
      → ∃ λ c → (extend Γ d ⊢ b ⇐ c) × _≈_ conv (tm-pi g d c) A
    lambda-checking {g = g} {d = d} (⇐-lam {c = c} kind checked) =
      c , checked , eq (tm-pi g d c)
    lambda-checking {g = g} {d = d} {A = A} (⇐-infer {T′ = B} der equal)
      with lambda-inference der
    ... | c , checked , between = c , checked , compose (tm-pi g d c) B A between equal
    lambda-checking {g = g} {d = d} {A = A} (⇐-conv {T = B} der equal)
      with lambda-checking der
    ... | c , checked , between = c , checked , compose (tm-pi g d c) B A between equal
    lambda-checking (⇐-cumul der le) with lambda-inference der
    ... | c , checked , between = ⊥-elim (pi-not-sort between)

    sort-inference : ∀ {n} {Γ : Ctx n} {l A}
      → Γ ⊢ tm-type l ⇒ A → ∃ λ j → _≈_ conv (tm-type j) A
    sort-inference (⇒-type {l′ = j} p) = j , eq (tm-type j)
    sort-inference {A = A} (⇒-conv {T = B} der equal) with sort-inference der
    ... | j , between = j , compose (tm-type j) B A between equal
    sort-inference (⇒-cumul {j = j} der le) = j , eq (tm-type j)
    sort-check-not-pi : ∀ {n} {Γ : Ctx n} {l A g d c}
      → Γ ⊢ tm-type l ⇐ A → _≈_ conv A (tm-pi g d c) → ⊥
    sort-check-not-pi {A = A} {g} {d} {c} (⇐-infer {T′ = B} der equal) target
      with sort-inference der
    ... | j , between = sort-not-pi
      (compose (tm-type j) A (tm-pi g d c) (compose (tm-type j) B A between equal) target)
    sort-check-not-pi {A = A} {g} {d} {c} (⇐-conv {T = B} der equal) target =
      sort-check-not-pi der (compose B A (tm-pi g d c) equal target)
    sort-check-not-pi (⇐-cumul der le) target = sort-not-pi target

    codomain : ∀ g d c g′ d′ c′ → _≈_ conv (tm-pi g d c) (tm-pi g′ d′ c′)
      → _≈_ conv c c′
    codomain g d c g′ d′ c′ equal = proj₂ (proj₂
      (≈-pi-components conv {g = g′} {d = d′} {c = c′} {g′ = g} {d′ = d} {c′ = c} equal))
    domain : ∀ g d c g′ d′ c′ → _≈_ conv (tm-pi g d c) (tm-pi g′ d′ c′)
      → _≈_ conv d d′
    domain g d c g′ d′ c′ equal = proj₁ (proj₂
      (≈-pi-components conv {g = g′} {d = d′} {c = c′} {g′ = g} {d′ = d} {c′ = c} equal))
