------------------------------------------------------------------------
-- Compatibility adapter retaining direct/evaluated execution routes.
-- Both routes embed into the shared recursive exact-case evaluator.
-- Exact names/arity only: no aliases, parameter filtering or erased slots.
-- Fuel bounds recursive height, not total work; exhaustion is not divergence.
------------------------------------------------------------------------
module Core.ClosureCase where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
import Data.String.Properties
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
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
  computed : ∀ {scrutinee name motive branches ar body values result}
    → E.Evaluates env scrutinee (E.v-ctor name values)
    → findBranch name branches ≡ just (name , ar , body)
    → length values ≡ ar
    → E.Evaluates (reverse values ++ env) body result
    → Executes env (tm-case scrutinee motive branches) result

fields-evaluated : ∀ {env args values} → Fields env args values → E.EvaluatesSpine env args values
fields-evaluated f[] = E.e[]
fields-evaluated (f∷ head rest) = E.e∷ head (fields-evaluated rest)

-- An evidence bridge, not equality of algorithms, proofs or fuel budgets.
as-computed : ∀ {env term value} → Executes env term value → Executes env term value
as-computed (executed fields found exact body) =
  computed (E.e-ctor (fields-evaluated fields)) found (trans (fields-length fields) exact) body
as-computed (computed scrutinee found exact body) = computed scrutinee found exact body

to-shared : ∀ {env term value} → Executes env term value → E.Evaluates env term value
to-shared (executed fields found exact body) =
  E.e-case (E.e-ctor (fields-evaluated fields)) found (trans (fields-length fields) exact) body
to-shared (computed scrutinee found exact body) = E.e-case scrutinee found exact body

data Route : Set where
  direct-route evaluated-route : Route
route : ∀ {env term value} → Executes env term value → Route
route (executed fields found exact body) = direct-route
route (computed scrutinee found exact body) = evaluated-route
as-computed-route : ∀ {env term value} (execution : Executes env term value)
  → route (as-computed execution) ≡ evaluated-route
as-computed-route (executed fields found exact body) = refl
as-computed-route (computed scrutinee found exact body) = refl

data Failure : Set where
  exhausted unsupported-head missing-branch arity-mismatch : Failure
  field-failure body-failure : E.Failure → Failure
  scrutinee-failure : E.Failure → Failure
  neutral-scrutinee non-constructor : Failure
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
dispatch : ∀ {env scrutinee} (fuel : ℕ) (motive : Term) (branches : List Branch) (value : E.Value)
  → E.Evaluates env scrutinee value → Result (Σ E.Value (Executes env (tm-case scrutinee motive branches)))
dispatch {env} fuel motive branches (E.v-ctor name values) evaluated
  with findBranch name branches in found
... | nothing = stop missing-branch
... | just (cn , ar , body) with name Data.String.Properties.≟ cn
... | no _ = stop missing-branch
... | yes refl with length values Nat.≟ ar
... | no _ = stop arity-mismatch
... | yes exact with E.run fuel body (reverse values ++ env)
... | E.stop reason = stop (body-failure reason)
... | E.done (result , body-evaluated) = done (result , computed evaluated found exact body-evaluated)
dispatch fuel motive branches (E.v-neutral head) evaluated = stop neutral-scrutinee
dispatch fuel motive branches other evaluated = stop non-constructor

run-computed : (fuel : ℕ) (scrutinee motive : Term) (branches : List Branch) (env : List E.Value)
  → Result (Σ E.Value (Executes env (tm-case scrutinee motive branches)))
run-computed zero scrutinee motive branches env = stop exhausted
run-computed (suc fuel) scrutinee motive branches env with E.run fuel scrutinee env
... | E.stop reason = stop (scrutinee-failure reason)
... | E.done (value , evaluated) = dispatch fuel motive branches value evaluated

-- Like actual Eval, evaluate fields before selecting the branch; motive
-- and unused branches are not evaluated. Preserve the original DIRECT
-- path's budgets/diagnostics; other case heads use evaluated scrutinees.
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
run (suc fuel) (tm-case scrutinee motive branches) env = run-computed (suc fuel) scrutinee motive branches env
run (suc fuel) other env = stop unsupported-head

