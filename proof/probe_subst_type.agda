module probe_subst_type where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Typing using (Context; _∋_at_; here; there; extend)

-- General substitution: Γ ∋ A at j, and we substitute index j.
-- The typing rule: if Γ ⊢ t ⇒ T and Γ ⊢ a ⇐ A (where Γ ∋ A at j),
-- then Γ ⊢ substT j a t ⇒ substT j a T.
-- Under a binder, j becomes suc j, and the context extends.
