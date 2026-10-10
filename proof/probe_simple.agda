module probe_simple where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wk)

-- With extend = prepend (no renaming), lengthCtx is definitional.
length-extend : ∀ Γ T → lengthCtx (extend Γ T) ≡ suc (lengthCtx Γ)
length-extend Γ T = refl

wkFin : ∀ Γ T → Fin (lengthCtx Γ) → Fin (lengthCtx (extend Γ T))
wkFin Γ T = suc

lookup-extend : ∀ {Γ} (T : Term) (i : Fin (lengthCtx Γ))
              → lookup (extend Γ T) (wkFin Γ T i) ≡ lookup Γ i
lookup-extend T i = refl
