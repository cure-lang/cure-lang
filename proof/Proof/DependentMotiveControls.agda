------------------------------------------------------------------------
-- Strict motive controls checked against an abstract conversion parameter,
-- then instantiated by DependentTypingControls on the concrete model.
------------------------------------------------------------------------
module Proof.DependentMotiveControls where

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
open import Core.Coverage
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.DependentTyping
import Proof.DependentTypingExamples as E
import Proof.DependentTypingInversion as Inversion

module Controls (conv : Conversion) where
  open Core.DependentTyping.Typing E.env E.sig conv
  open Inversion.Laws E.env E.sig conv
  open Conversion

  tail₁ tail₂ tail₃ : Term
  tail₃ = tm-pi unrestricted E.scrutinee-domain (tm-type l0)
  tail₂ = tm-pi unrestricted (tm-var 0) tail₃
  tail₁ = tm-pi unrestricted (tm-type l0) tail₂

  unary : Term
  unary = tm-lam unrestricted tm-atom_type (tm-type l0)
  abstract
    unary-rejected : ∀ {n} {Γ : Ctx n} → Motive Γ E.family (tm-atom_type ∷ []) unary l0 → ⊥
    unary-rejected (motive scoped kind typed) with lambda-inference typed
    ... | c , checked , between =
      sort-check-not-pi checked (codomain unrestricted tm-atom_type c unrestricted tm-atom_type tail₁ between)

  -- This is the executable's ACCEPTED extensional motive with the wrong
  -- annotation at the scrutinee lambda, not a claimed kernel exploit.
  extensional : Term
  extensional = tm-lam unrestricted tm-atom_type
    (tm-lam unrestricted (tm-type l0) (tm-lam unrestricted (tm-var 0)
      (tm-lam unrestricted tm-atom_type (tm-var 2))))
  abstract
    misannotation : ∀ c₀ c₁ c₂ c₃
      → _≈_ conv (tm-pi unrestricted tm-atom_type c₀)
          (motiveType E.family (tm-atom_type ∷ []) l0)
      → _≈_ conv (tm-pi unrestricted (tm-type l0) c₁) c₀
      → _≈_ conv (tm-pi unrestricted (tm-var 0) c₂) c₁
      → _≈_ conv (tm-pi unrestricted tm-atom_type c₃) c₂ → ⊥
    misannotation c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃
      with ≈-heads conv {t = tm-atom_type} {u = E.scrutinee-domain} ty-atom ty-data
        (domain unrestricted tm-atom_type c₃ unrestricted E.scrutinee-domain (tm-type l0)
          (compose (tm-pi unrestricted tm-atom_type c₃) c₂ tail₃ e₃
            (codomain unrestricted (tm-var 0) c₂ unrestricted (tm-var 0) tail₃
              (compose (tm-pi unrestricted (tm-var 0) c₂) c₁ tail₂ e₂
                (codomain unrestricted (tm-type l0) c₁ unrestricted (tm-type l0) tail₂
                  (compose (tm-pi unrestricted (tm-type l0) c₁) c₀ tail₁ e₁
                    (codomain unrestricted tm-atom_type c₀ unrestricted tm-atom_type tail₁ e₀)))))))
    ... | ()
    extensional-rejected : ∀ {n} {Γ : Ctx n}
      → Motive Γ E.family (tm-atom_type ∷ []) extensional l0 → ⊥
    extensional-rejected (motive scoped kind typed) with lambda-inference typed
    ... | c₀ , checked₀ , e₀ with lambda-checking checked₀
    ... | c₁ , checked₁ , e₁ with lambda-checking checked₁
    ... | c₂ , checked₂ , e₂ with lambda-checking checked₂
    ... | c₃ , checked₃ , e₃ = misannotation c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃
