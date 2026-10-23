------------------------------------------------------------------------
-- Positive evaluation MODEL for functions, lets, constructors and exact cases.
-- Every recursive eval/apply call consumes height fuel. Exhaustion is
-- NOT divergence, nor a bound on total work or executable Elixir fuel.
------------------------------------------------------------------------
module Core.ClosureEval where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Name; Term; tm-type; tm-atom_type; tm-atom_lit; tm-global;
  Branch; tm-var; tm-pi; tm-lam; tm-app; tm-let; tm-ctor; tm-case)
open import Core.Reduction using (findBranch)
import Data.Nat.Properties as Nat
import Data.String.Properties
open import Relation.Nullary using (yes; no)
open import Core.Grade using (Grade)
open import Core.Universe using (Level)

mutual
  data Value : Set where
    v-type : Level → Value
    v-atom-type : Value
    v-atom : Name → Value
    v-pi v-lam : Grade → Value → List Value → Term → Value
    v-ctor : Name → List Value → Value
    v-neutral : Neutral → Value
  data Neutral : Set where
    n-var : ℕ → Neutral
    n-global : Name → Neutral
    n-app : Neutral → Value → Neutral

lookup-value : List Value → ℕ → Maybe Value
lookup-value [] k = nothing
lookup-value (v ∷ env) zero = just v
lookup-value (v ∷ env) (suc k) = lookup-value env k

mutual
  data Evaluates (env : List Value) : Term → Value → Set where
    e-type : ∀ {l} → Evaluates env (tm-type l) (v-type l)
    e-atom-type : Evaluates env tm-atom_type v-atom-type
    e-atom : ∀ {name} → Evaluates env (tm-atom_lit name) (v-atom name)
    e-global : ∀ {name} → Evaluates env (tm-global name) (v-neutral (n-global name))
    e-var : ∀ {k v} → lookup-value env k ≡ just v → Evaluates env (tm-var k) v
    e-pi : ∀ {g domain codomain value}
      → Evaluates env domain value → Evaluates env (tm-pi g domain codomain) (v-pi g value env codomain)
    e-lam : ∀ {g domain body value}
      → Evaluates env domain value → Evaluates env (tm-lam g domain body) (v-lam g value env body)
    e-ctor : ∀ {name args values} → EvaluatesSpine env args values
      → Evaluates env (tm-ctor name args) (v-ctor name values)
    e-app : ∀ {function argument vf va value}
      → Evaluates env function vf → Evaluates env argument va → Applies vf va value
      → Evaluates env (tm-app function argument) value
    -- The annotation is deliberately not evaluated, like actual Eval.
    e-let : ∀ {g ty value body actual result}
      → Evaluates env value actual → Evaluates (actual ∷ env) body result
      → Evaluates env (tm-let g ty value body) result
    e-case : ∀ {scrutinee motive branches name values ar body result}
      → Evaluates env scrutinee (v-ctor name values)
      → findBranch name branches ≡ just (name , ar , body)
      → length values ≡ ar
      → Evaluates (reverse values ++ env) body result
      → Evaluates env (tm-case scrutinee motive branches) result
  data Applies : Value → Value → Value → Set where
    a-closure : ∀ {g domain env body argument value}
      → Evaluates (argument ∷ env) body value → Applies (v-lam g domain env body) argument value
    a-neutral : ∀ {neutral argument}
      → Applies (v-neutral neutral) argument (v-neutral (n-app neutral argument))
  data EvaluatesSpine (env : List Value) : List Term → List Value → Set where
    e[] : EvaluatesSpine env [] []
    e∷ : ∀ {term terms value values} → Evaluates env term value → EvaluatesSpine env terms values
      → EvaluatesSpine env (term ∷ terms) (value ∷ values)

data Failure : Set where
  exhausted unsupported unbound non-function : Failure
  missing-branch arity-mismatch neutral-scrutinee non-constructor : Failure
  -- Companion readback rejects escaped levels.
  escaped-level : Failure
data Result (A : Set) : Set where
  done : A → Result A
  stop : Failure → Result A

mutual
  run : (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
  run zero term env = stop exhausted
  run (suc fuel) (tm-type l) env = done (v-type l , e-type)
  run (suc fuel) tm-atom_type env = done (v-atom-type , e-atom-type)
  run (suc fuel) (tm-atom_lit name) env = done (v-atom name , e-atom)
  run (suc fuel) (tm-global name) env = done (v-neutral (n-global name) , e-global)
  run (suc fuel) (tm-var k) env with lookup-value env k in found
  ... | nothing = stop unbound
  ... | just value = done (value , e-var found)
  run (suc fuel) (tm-pi g domain codomain) env with run fuel domain env
  ... | stop reason = stop reason
  ... | done (value , evaluated) = done (v-pi g value env codomain , e-pi evaluated)
  run (suc fuel) (tm-lam g domain body) env with run fuel domain env
  ... | stop reason = stop reason
  ... | done (value , evaluated) = done (v-lam g value env body , e-lam evaluated)
  run (suc fuel) (tm-ctor name args) env with run-spine fuel args env
  ... | stop reason = stop reason
  ... | done (values , evaluated) = done (v-ctor name values , e-ctor evaluated)
  run (suc fuel) (tm-app function argument) env with run fuel function env
  ... | stop reason = stop reason
  ... | done (vf , function-evaluated) with run fuel argument env
  ... | stop reason = stop reason
  ... | done (va , argument-evaluated) with apply fuel vf va
  ... | stop reason = stop reason
  ... | done (value , applied) = done (value , e-app function-evaluated argument-evaluated applied)
  run (suc fuel) (tm-let g ty value body) env with run fuel value env
  ... | stop reason = stop reason
  ... | done (actual , value-evaluated) with run fuel body (actual ∷ env)
  ... | stop reason = stop reason
  ... | done (result , body-evaluated) = done (result , e-let value-evaluated body-evaluated)
  run (suc fuel) (tm-case scrutinee motive branches) env with run fuel scrutinee env
  ... | stop reason = stop reason
  ... | done (value , evaluated) = case-apply fuel motive branches value evaluated
  run (suc fuel) other env = stop unsupported

  apply : (fuel : ℕ) (function argument : Value) → Result (Σ Value (Applies function argument))
  apply zero function argument = stop exhausted
  apply (suc fuel) (v-lam g domain env body) argument with run fuel body (argument ∷ env)
  ... | stop reason = stop reason
  ... | done (value , evaluated) = done (value , a-closure evaluated)
  apply (suc fuel) (v-neutral neutral) argument = done (v-neutral (n-app neutral argument) , a-neutral)
  apply (suc fuel) other argument = stop non-function

  run-spine : (fuel : ℕ) (terms : List Term) (env : List Value)
    → Result (Σ (List Value) (EvaluatesSpine env terms))
  run-spine zero terms env = stop exhausted
  run-spine (suc fuel) [] env = done ([] , e[])
  run-spine (suc fuel) (term ∷ terms) env with run fuel term env
  ... | stop reason = stop reason
  ... | done (value , evaluated) with run-spine fuel terms env
  ... | stop reason = stop reason
  ... | done (values , rest) = done (value ∷ values , e∷ evaluated rest)

  case-apply : ∀ {env scrutinee} (fuel : ℕ) (motive : Term) (branches : List Branch) (value : Value)
    → Evaluates env scrutinee value → Result (Σ Value (Evaluates env (tm-case scrutinee motive branches)))
  case-apply {env} zero motive branches value evaluated = stop exhausted
  case-apply {env} (suc fuel) motive branches (v-ctor name values) evaluated
    with findBranch name branches in found
  ... | nothing = stop missing-branch
  ... | just (cn , ar , body) with name Data.String.Properties.≟ cn
  ... | no _ = stop missing-branch
  ... | yes refl with length values Nat.≟ ar
  ... | no _ = stop arity-mismatch
  ... | yes exact with run fuel body (reverse values ++ env)
  ... | stop reason = stop reason
  ... | done (result , body-evaluated) = done (result , e-case evaluated found exact body-evaluated)
  case-apply (suc fuel) motive branches (v-neutral head) evaluated = stop neutral-scrutinee
  case-apply (suc fuel) motive branches other evaluated = stop non-constructor
