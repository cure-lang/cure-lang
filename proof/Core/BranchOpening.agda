------------------------------------------------------------------------
-- Fresh branch opening MODEL, not constructor contraction or field typing.
-- Semantic depth is arity + caller depth; arithmetic agreement with the
-- executable's depth + arity is proved separately. Fuel is height only.
------------------------------------------------------------------------
module Core.BranchOpening where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax using (Term)
open import Core.Signature using (IndEnv)
import Core.ClosureEval as E

fresh : ℕ → E.Value
fresh level = E.v-neutral (E.n-var level)
prefix : (depth arity : ℕ) → List E.Value
prefix depth zero = []
prefix depth (suc arity) = fresh (arity + depth) ∷ prefix depth arity
environment : (depth arity : ℕ) → List E.Value → List E.Value
environment depth arity env = prefix depth arity ++ env
-- Declaration order, matching the executable's finite range of offsets.
forward : (depth arity : ℕ) → List E.Value
forward depth zero = []
forward depth (suc arity) = forward depth arity ++ fresh (depth + arity) ∷ []
environment-length : ∀ depth arity env → length (environment depth arity env) ≡ arity + length env
environment-length depth zero env = refl
environment-length depth (suc arity) env = cong suc (environment-length depth arity env)

run : (fuel depth arity : ℕ) (env : List E.Value) (body : Term)
  → E.Result (Σ E.Value (E.Evaluates (environment depth arity env) body))
run fuel depth arity env body = E.run fuel body (environment depth arity env)
run-with : IndEnv → (fuel depth arity : ℕ) (env : List E.Value) (body : Term)
  → E.Result (Σ E.Value (E.Evaluates (environment depth arity env) body))
run-with ind fuel depth arity env body = E.run-with ind fuel body (environment depth arity env)
