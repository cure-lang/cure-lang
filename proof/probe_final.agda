module probe_final where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Proof.Substitution using (rename-id; rename-cong; ext-id)

-- Global convention: extend renames existing types by wk.
wk : Ren
wk k = suc k

data Ctx : Set where
  ⟨⟩  : Ctx
  _▷_ : Ctx → Term → Ctx

lengthCtx : Ctx → ℕ
lengthCtx ⟨⟩ = 0
lengthCtx (Γ ▷ T) = suc (lengthCtx Γ)

extend : Ctx → Term → Ctx
extend ⟨⟩ T = ⟨⟩ ▷ T
extend (Γ ▷ U) T = extend Γ T ▷ rename wk U

lookup : (Γ : Ctx) → Fin (lengthCtx Γ) → Term
lookup (Γ ▷ T) zero = T
lookup (Γ ▷ T) (suc i) = lookup Γ i

-- wkFin by transport.
length-extend : ∀ Γ T → lengthCtx (extend Γ T) ≡ suc (lengthCtx Γ)
length-extend ⟨⟩ T = refl
length-extend (Γ ▷ U) T = cong suc (length-extend Γ T)

wkFin : ∀ Γ T → Fin (lengthCtx Γ) → Fin (lengthCtx (extend Γ T))
wkFin Γ T i = subst (λ n → Fin n) (sym (length-extend Γ T)) (suc i)

-- The lookup law. The head case: lookup (extend (Γ ▷ U) T) (wkFin ... zero)
-- = lookup (extend Γ T ▷ rename wk U) (transported suc zero).
-- The transported suc zero should be index 1 of the extended context,
-- which is lookup (extend Γ T) zero = ... hmm, this is the tail.
-- Actually wkFin (Γ ▷ U) T zero = subst Fin (sym (cong suc (length-extend Γ T))) (suc zero)
--   : Fin (suc (lengthCtx (extend Γ T))) = Fin (lengthCtx (extend Γ T ▷ rename wk U))
-- lookup of index (suc zero) in (extend Γ T ▷ rename wk U) = lookup (extend Γ T) zero = U? No.
-- Hmm, suc zero in Fin (suc (lengthCtx (extend Γ T))) is index 1, which is
-- lookup (extend Γ T) zero. And lookup (extend Γ T) zero = ... depends.

-- This is getting complicated. Let me just check the head case directly.
