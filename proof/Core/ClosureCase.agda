------------------------------------------------------------------------
-- Separate positive constructor-headed case MODEL. Fields and selected
-- bodies use ClosureEval, not a new arbitrary-scrutinee evaluator.
-- Exact names/arity only: no aliases, parameter filtering or erased slots.
------------------------------------------------------------------------
module Core.ClosureCase where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
import Data.String.Properties
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)
open import Core.Syntax
open import Core.Reduction using (findBranch)
import Core.ClosureEval as E

data Fields (env : List E.Value) : List Term → List E.Value → Set where
  f[] : Fields env [] []
  f∷ : ∀ {term terms value values} → E.Evaluates env term value
    → Fields env terms values → Fields env (term ∷ terms) (value ∷ values)

fields-length : ∀ {env terms values} → Fields env terms values → length values ≡ length terms
fields-length f[] = refl
fields-length (f∷ head rest) = cong suc (fields-length rest)

data Executes (env : List E.Value) : Term → E.Value → Set where
  executed : ∀ {name args motive branches ar body values result}
    → Fields env args values
    → findBranch name branches ≡ just (name , ar , body)
    → length args ≡ ar
    → E.Evaluates (reverse values ++ env) body result
    → Executes env (tm-case (tm-ctor name args) motive branches) result

data Failure : Set where
  exhausted unsupported-head missing-branch arity-mismatch : Failure
  field-failure body-failure : E.Failure → Failure
data Result (A : Set) : Set where
  done : A → Result A
  stop : Failure → Result A

fields : (fuel : ℕ) (terms : List Term) (env : List E.Value)
  → Result (Σ (List E.Value) (Fields env terms))
fields zero terms env = stop exhausted
fields (suc fuel) [] env = done ([] , f[])
fields (suc fuel) (term ∷ terms) env with E.run fuel term env
... | E.stop reason = stop (field-failure reason)
... | E.done (value , evaluated) with fields fuel terms env
... | stop reason = stop reason
... | done (values , rest) = done (value ∷ values , f∷ evaluated rest)

-- Like actual Eval, evaluate fields before selecting the branch; motive
-- and unused branches are not evaluated. Fuel bounds height, not work.
run : (fuel : ℕ) (term : Term) (env : List E.Value)
  → Result (Σ E.Value (Executes env term))
run zero term env = stop exhausted
run (suc fuel) (tm-case (tm-ctor name args) motive branches) env with fields fuel args env
... | stop reason = stop reason
... | done (values , evaluated) with findBranch name branches in found
... | nothing = stop missing-branch
... | just (cn , ar , body) with name Data.String.Properties.≟ cn
... | no _ = stop missing-branch
... | yes refl with length args Nat.≟ ar
... | no _ = stop arity-mismatch
... | yes exact with E.run fuel body (reverse values ++ env)
... | E.stop reason = stop (body-failure reason)
... | E.done (value , body-evaluated) =
  done (value , executed evaluated found exact body-evaluated)
run (suc fuel) other env = stop unsupported-head

