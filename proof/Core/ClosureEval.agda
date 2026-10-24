------------------------------------------------------------------------
-- Positive evaluation MODEL for functions, lets, constructors and exact cases.
-- Data uses explicit signature-aware entry points; source splits are checked.
-- Residual case capture is opt-in and propagates through every worker.
-- Every recursive eval/apply call consumes height fuel. Exhaustion is
-- NOT divergence, nor a bound on total work or executable Elixir fuel.
------------------------------------------------------------------------
module Core.ClosureEval where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Core.Syntax using (Name; Term; tm-type; tm-atom_type; tm-atom_lit; tm-global;
  Branch; tm-var; tm-pi; tm-lam; tm-app; tm-let; tm-ctor; tm-case; tm-data)
open import Core.Signature using (IndEnv)
import Core.DataSpine as Layout
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
    v-data : Name → List Value → List Value → Value
    v-neutral : Neutral → Value
  data Neutral : Set where
    n-var : ℕ → Neutral
    n-global : Name → Neutral
    n-app : Neutral → Value → Neutral
    -- All raw branch bodies and the motive capture this SAME caller.
    n-case : Neutral → List Value → Term → List Branch → Neutral

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
    e-data : ∀ {name ps is pvs ivs} → EvaluatesSpine env ps pvs → EvaluatesSpine env is ivs
      → Evaluates env (tm-data name ps is) (v-data name pvs ivs)
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
    e-neutral-case : ∀ {scrutinee motive branches head}
      → Evaluates env scrutinee (v-neutral head)
      → Evaluates env (tm-case scrutinee motive branches)
          (v-neutral (n-case head env motive branches))
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
  data-layout : Layout.Failure → Failure
data Result (A : Set) : Set where
  done : A → Result A
  stop : Failure → Result A

spine-length : ∀ {env args values} → EvaluatesSpine env args values → length values ≡ length args
spine-length e[] = refl
spine-length (e∷ head rest) = cong suc (spine-length rest)
evaluated-layout : ∀ {ind name env ps is pvs ivs} → Layout.SourceLayout ind name ps is
  → EvaluatesSpine env ps pvs → EvaluatesSpine env is ivs → Layout.SourceLayout ind name pvs ivs
evaluated-layout layout params indices = Layout.source-layout
  (Layout.SourceLayout.family layout) (Layout.SourceLayout.found layout)
  (trans (spine-length params) (Layout.SourceLayout.parameter-count layout))
  (trans (spine-length indices) (Layout.SourceLayout.index-count layout))

mutual
  run-config : (residual : Bool) → (mode : Maybe IndEnv) → (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
  run-config residual mode zero term env = stop exhausted
  run-config residual mode (suc fuel) (tm-type l) env = done (v-type l , e-type)
  run-config residual mode (suc fuel) tm-atom_type env = done (v-atom-type , e-atom-type)
  run-config residual mode (suc fuel) (tm-atom_lit name) env = done (v-atom name , e-atom)
  run-config residual mode (suc fuel) (tm-global name) env = done (v-neutral (n-global name) , e-global)
  run-config residual mode (suc fuel) (tm-var k) env with lookup-value env k in found
  ... | nothing = stop unbound
  ... | just value = done (value , e-var found)
  run-config residual mode (suc fuel) (tm-pi g domain codomain) env with run-config residual mode fuel domain env
  ... | stop reason = stop reason
  ... | done (value , evaluated) = done (v-pi g value env codomain , e-pi evaluated)
  run-config residual mode (suc fuel) (tm-lam g domain body) env with run-config residual mode fuel domain env
  ... | stop reason = stop reason
  ... | done (value , evaluated) = done (v-lam g value env body , e-lam evaluated)
  run-config residual mode (suc fuel) (tm-ctor name args) env with spine-config residual mode fuel args env
  ... | stop reason = stop reason
  ... | done (values , evaluated) = done (v-ctor name values , e-ctor evaluated)
  run-config residual nothing (suc fuel) (tm-data name ps is) env = stop unsupported
  run-config residual (just ind) (suc fuel) (tm-data name ps is) env with Layout.check-source ind name ps is
  ... | Layout.rejected reason = stop (data-layout reason)
  ... | Layout.accepted layout with spine-config residual (just ind) fuel ps env
  ... | stop reason = stop reason
  ... | done (pvs , params) with spine-config residual (just ind) fuel is env
  ... | stop reason = stop reason
  ... | done (ivs , indices) = done (v-data name pvs ivs , e-data params indices)
  run-config residual mode (suc fuel) (tm-app function argument) env with run-config residual mode fuel function env
  ... | stop reason = stop reason
  ... | done (vf , function-evaluated) with run-config residual mode fuel argument env
  ... | stop reason = stop reason
  ... | done (va , argument-evaluated) with apply-config residual mode fuel vf va
  ... | stop reason = stop reason
  ... | done (value , applied) = done (value , e-app function-evaluated argument-evaluated applied)
  run-config residual mode (suc fuel) (tm-let g ty value body) env with run-config residual mode fuel value env
  ... | stop reason = stop reason
  ... | done (actual , value-evaluated) with run-config residual mode fuel body (actual ∷ env)
  ... | stop reason = stop reason
  ... | done (result , body-evaluated) = done (result , e-let value-evaluated body-evaluated)
  run-config residual mode (suc fuel) (tm-case scrutinee motive branches) env with run-config residual mode fuel scrutinee env
  ... | stop reason = stop reason
  ... | done (value , evaluated) = case-config residual mode fuel motive branches value evaluated
  run-config residual mode (suc fuel) other env = stop unsupported

  apply-config : (residual : Bool) → (mode : Maybe IndEnv) → (fuel : ℕ) (function argument : Value) → Result (Σ Value (Applies function argument))
  apply-config residual mode zero function argument = stop exhausted
  apply-config residual mode (suc fuel) (v-lam g domain env body) argument with run-config residual mode fuel body (argument ∷ env)
  ... | stop reason = stop reason
  ... | done (value , evaluated) = done (value , a-closure evaluated)
  apply-config residual mode (suc fuel) (v-neutral neutral) argument = done (v-neutral (n-app neutral argument) , a-neutral)
  apply-config residual mode (suc fuel) other argument = stop non-function

  spine-config : (residual : Bool) → (mode : Maybe IndEnv) → (fuel : ℕ) (terms : List Term) (env : List Value)
    → Result (Σ (List Value) (EvaluatesSpine env terms))
  spine-config residual mode zero terms env = stop exhausted
  spine-config residual mode (suc fuel) [] env = done ([] , e[])
  spine-config residual mode (suc fuel) (term ∷ terms) env with run-config residual mode fuel term env
  ... | stop reason = stop reason
  ... | done (value , evaluated) with spine-config residual mode fuel terms env
  ... | stop reason = stop reason
  ... | done (values , rest) = done (value ∷ values , e∷ evaluated rest)

  case-config : (residual : Bool) → (mode : Maybe IndEnv) → ∀ {env scrutinee} (fuel : ℕ) (motive : Term) (branches : List Branch) (value : Value)
    → Evaluates env scrutinee value → Result (Σ Value (Evaluates env (tm-case scrutinee motive branches)))
  case-config residual mode {env} zero motive branches value evaluated = stop exhausted
  case-config residual mode {env} (suc fuel) motive branches (v-ctor name values) evaluated
    with findBranch name branches in found
  ... | nothing = stop missing-branch
  ... | just (cn , ar , body) with name Data.String.Properties.≟ cn
  ... | no _ = stop missing-branch
  ... | yes refl with length values Nat.≟ ar
  ... | no _ = stop arity-mismatch
  ... | yes exact with run-config residual mode fuel body (reverse values ++ env)
  ... | stop reason = stop reason
  ... | done (result , body-evaluated) = done (result , e-case evaluated found exact body-evaluated)
  case-config false mode (suc fuel) motive branches (v-neutral head) evaluated = stop neutral-scrutinee
  case-config true mode {env} (suc fuel) motive branches (v-neutral head) evaluated =
    done (v-neutral (n-case head env motive branches) , e-neutral-case evaluated)
  case-config residual mode (suc fuel) motive branches other evaluated = stop non-constructor

-- Compatibility workers retain residual exclusion at EVERY recursive call.
run-in : Maybe IndEnv → (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
run-in = run-config false
apply-in : Maybe IndEnv → (fuel : ℕ) (function argument : Value) → Result (Σ Value (Applies function argument))
apply-in = apply-config false
run-spine-in : Maybe IndEnv → (fuel : ℕ) (terms : List Term) (env : List Value)
  → Result (Σ (List Value) (EvaluatesSpine env terms))
run-spine-in = spine-config false
case-apply-in : Maybe IndEnv → ∀ {env scrutinee} (fuel : ℕ) (motive : Term) (branches : List Branch) (value : Value)
  → Evaluates env scrutinee value → Result (Σ Value (Evaluates env (tm-case scrutinee motive branches)))
case-apply-in = case-config false

-- Opt-in residual evaluation propagates through closures, spines and exact cases.
run-residual-in : Maybe IndEnv → (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
run-residual-in = run-config true
run-residual : (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
run-residual = run-residual-in nothing
run-residual-with : IndEnv → (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
run-residual-with ind = run-residual-in (just ind)

-- Compatibility entry points retain signature-free data exclusion.
run : (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
run = run-in nothing
apply : (fuel : ℕ) (function argument : Value) → Result (Σ Value (Applies function argument))
apply = apply-in nothing
run-spine : (fuel : ℕ) (terms : List Term) (env : List Value)
  → Result (Σ (List Value) (EvaluatesSpine env terms))
run-spine = run-spine-in nothing
case-apply : ∀ {env scrutinee} (fuel : ℕ) (motive : Term) (branches : List Branch) (value : Value)
  → Evaluates env scrutinee value → Result (Σ Value (Evaluates env (tm-case scrutinee motive branches)))
case-apply = case-apply-in nothing
run-with : IndEnv → (fuel : ℕ) (term : Term) (env : List Value) → Result (Σ Value (Evaluates env term))
run-with ind = run-in (just ind)
apply-with : IndEnv → (fuel : ℕ) (function argument : Value) → Result (Σ Value (Applies function argument))
apply-with ind = apply-in (just ind)
run-spine-with : IndEnv → (fuel : ℕ) (terms : List Term) (env : List Value)
  → Result (Σ (List Value) (EvaluatesSpine env terms))
run-spine-with ind = run-spine-in (just ind)
