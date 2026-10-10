module probe_substfinal where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Core.Syntax
open import Core.Typing using (Context; ⟨⟩; _▷_; lengthCtx; lookup; extend; wk; wkFin; Conversion)
open import Proof.Substitution using (subst-id; subst-var-eq; subst-var-neq; <-false)
open import Proof.Context using (lookup-head; lookup-extend)

-- pred renaming: index 0 ↦ 0, suc k ↦ k.
pred : Ren
pred zero = zero
pred (suc k) = k

substTop : Term → Term → Term
substTop a t = rename pred (substT 0 a t)

-- The ⇒-var zero case: substTop a (var 0) = rename pred (substT 0 a (var 0))
--   = rename pred a. Hmm — it's `rename pred a`, not `a`!
-- The term `var 0` becomes `a`, but then `rename pred` is applied to `a`.
-- That's because `substT 0 a (var 0) = a`, and then `rename pred a`.
-- But `a` lives in Γ, and `rename pred a` would renumber a's variables —
-- which is wrong! `a` should be inserted as-is.
--
-- So `substTop` should NOT apply `rename pred` to the substituted `a`.
-- The correct operation: `substT 0 a` then rename pred ONLY the parts that
-- came from `t`, not from `a`. This requires a "simultaneous" substitution.
