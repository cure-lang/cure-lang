module probe_gsubst where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend)

-- General substitution: substitute index j in a term, where the context
-- has A at index j. Under a binder, j becomes suc j.
-- The key: substT j a t, and the context is unchanged (the binder is added
-- inside the term, not the context).

-- For the ⇒-var case at index j: if the looked-up index is j, the result
-- is a; else it's the variable. With the function lookup, this is clean.
