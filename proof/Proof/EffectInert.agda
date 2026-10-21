------------------------------------------------------------------------
-- Inert Core effects: every reduction preserves the outer effect former.
-- No typing, coverage, conversion or signature-well-formedness assumption
-- is used. Child reductions are allowed; monad-law reductions are not.
------------------------------------------------------------------------
module Proof.EffectInert where

open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Reduction

effect-type-step : ∀ sig {a u}
  → _⇝_ sig (tm-effect_type a) u
  → ∃ λ a′ → u ≡ tm-effect_type a′ × _⇝_ sig a a′
effect-type-step sig (ξ-effect_type step) = _ , refl , step

effect-pure-step : ∀ sig {a u}
  → _⇝_ sig (tm-effect_pure a) u
  → ∃ λ a′ → u ≡ tm-effect_pure a′ × _⇝_ sig a a′
effect-pure-step sig (ξ-effect_pure step) = _ , refl , step

effect-bind-step : ∀ sig {e k u}
  → _⇝_ sig (tm-effect_bind e k) u
  → (∃ λ e′ → u ≡ tm-effect_bind e′ k × _⇝_ sig e e′)
    ⊎ (∃ λ k′ → u ≡ tm-effect_bind e k′ × _⇝_ sig k k′)
effect-bind-step sig (ξ-effect_bind₁ step) = inj₁ (_ , refl , step)
effect-bind-step sig (ξ-effect_bind₂ step) = inj₂ (_ , refl , step)

-- The property persists along arbitrary finite reduction sequences.
effect-type-steps : ∀ sig {a u}
  → _⇝*_ sig (tm-effect_type a) u
  → ∃ λ a′ → u ≡ tm-effect_type a′ × _⇝*_ sig a a′
effect-type-steps sig ⇝*-refl = _ , refl , ⇝*-refl
effect-type-steps sig (⇝*-step step rest) with effect-type-step sig step
... | a′ , refl , child with effect-type-steps sig rest
... | a″ , refl , children = a″ , refl , ⇝*-step child children

effect-pure-steps : ∀ sig {a u}
  → _⇝*_ sig (tm-effect_pure a) u
  → ∃ λ a′ → u ≡ tm-effect_pure a′ × _⇝*_ sig a a′
effect-pure-steps sig ⇝*-refl = _ , refl , ⇝*-refl
effect-pure-steps sig (⇝*-step step rest) with effect-pure-step sig step
... | a′ , refl , child with effect-pure-steps sig rest
... | a″ , refl , children = a″ , refl , ⇝*-step child children

effect-bind-steps : ∀ sig {e k u}
  → _⇝*_ sig (tm-effect_bind e k) u
  → ∃ λ e′ → ∃ λ k′
    → u ≡ tm-effect_bind e′ k′ × _⇝*_ sig e e′ × _⇝*_ sig k k′
effect-bind-steps sig ⇝*-refl = _ , _ , refl , ⇝*-refl , ⇝*-refl
effect-bind-steps sig (⇝*-step step rest) with effect-bind-step sig step
... | inj₁ (e′ , refl , child) with effect-bind-steps sig rest
... | e″ , k′ , refl , es , ks = e″ , k′ , refl , ⇝*-step child es , ks
effect-bind-steps sig (⇝*-step step rest) | inj₂ (k′ , refl , child)
  with effect-bind-steps sig rest
... | e′ , k″ , refl , es , ks = e′ , k″ , refl , es , ⇝*-step child ks
