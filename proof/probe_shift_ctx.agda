module probe_shift_ctx where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Core.Syntax
open import Core.Typing using (Context; _∋_at_; here; there; extend)

-- The shift-based weakening. Key: the target context is
-- `S ∷ shiftCtx 1 0 Γ`, and under a binder we need
-- `shift 1 0 d ∷ S ∷ shiftCtx 1 0 Γ` to equal `S ∷ shiftCtx 1 0 (d ∷ Γ)`.
-- These differ by a swap. So the statement must put S at the END.

-- Alternative: append S at the end (outermost). Then no type shifts.
-- Γ ∋ T at k → (Γ ++ [S]) ∋ T at k.
append-mor : ∀ {Γ T k} (S : Term) → Γ ∋ T at k → (Γ ++ (S ∷ [])) ∋ T at k
append-mor S here = here
append-mor S (there p) = there (append-mor S p)

-- But then the term doesn't shift, so weakening is trivial.
-- The substitution lemma needs the term to shift because we go under binders.
