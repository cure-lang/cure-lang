module probe_sub where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wkFin)

-- General substitution: substitute index j. The context keeps A at index j.
-- Under a binder, j becomes suc j, and the substituted term is shifted.
-- The lookup law: lookup Γ k, after substituting j, becomes substT j a (lookup Γ k)
-- for k ≠ j, and for k = j it becomes a.

-- The key structural fact: substituting at j and then looking up at k
-- (k ≠ j) equals looking up and substituting. This needs the types to be
-- "j-free" which holds for well-formed contexts.

-- For the head case (k = j): the type A is the substituted variable's type,
-- and we need substT j a A ≡ A, i.e. A is j-free.
