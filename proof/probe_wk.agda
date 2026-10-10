module probe_wk where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Core.Syntax
open import Core.Typing using (Context; _∋_at_; here; there; extend)

-- Weakening with the fresh binder at the END (outermost), so existing
-- indices and types are unchanged. The term shifts because... it doesn't.
-- So instead: weaken by inserting the binder and shifting the term.
-- The morphism: ρ k = k (identity), target = Γ ++ [S].
-- Term unchanged. This is "weakening by an unused variable" — trivially
-- type-preserving but useless.

-- The USEFUL weakening inserts S at the FRONT and shifts indices.
-- ρ = suc. Target = S ∷ Γ (types unshifted, since they're Γ-scoped and
-- the binder is at index 0, so existing types' free vars < |Γ| map to
-- themselves under suc... NO, they map k → suc k).
