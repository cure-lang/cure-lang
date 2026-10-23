------------------------------------------------------------------------
-- Scope for semantic closures includes their CAPTURED BODY syntax.
-- This is not semantic typing, termination or a Quote correctness axiom.
------------------------------------------------------------------------
module Core.ClosureScope where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature using (nothing≠just; just-inj)
import Core.ClosureEval as E

mutual
  data ValueScoped (depth : ℕ) : E.Value → Set where
    s-type : ∀ {l} → ValueScoped depth (E.v-type l)
    s-atom-type : ValueScoped depth E.v-atom-type
    s-atom : ∀ {name} → ValueScoped depth (E.v-atom name)
    s-pi : ∀ {g domain env body} → ValueScoped depth domain → EnvironmentScoped depth env
      → Scoped (suc (length env)) body → ValueScoped depth (E.v-pi g domain env body)
    s-lam : ∀ {g domain env body} → ValueScoped depth domain → EnvironmentScoped depth env
      → Scoped (suc (length env)) body → ValueScoped depth (E.v-lam g domain env body)
    s-neutral : ∀ {neutral} → NeutralScoped depth neutral → ValueScoped depth (E.v-neutral neutral)
  data EnvironmentScoped (depth : ℕ) : List E.Value → Set where
    s[] : EnvironmentScoped depth []
    s∷ : ∀ {value env} → ValueScoped depth value → EnvironmentScoped depth env
      → EnvironmentScoped depth (value ∷ env)
  data NeutralScoped (depth : ℕ) : E.Neutral → Set where
    s-var : ∀ {level} → level < depth → NeutralScoped depth (E.n-var level)
    s-global : ∀ {name} → NeutralScoped depth (E.n-global name)
    s-app : ∀ {function argument} → NeutralScoped depth function → ValueScoped depth argument
      → NeutralScoped depth (E.n-app function argument)

mutual
  raise-value : ∀ {d value} → ValueScoped d value → ValueScoped (suc d) value
  raise-value s-type = s-type
  raise-value s-atom-type = s-atom-type
  raise-value s-atom = s-atom
  raise-value (s-pi domain env body) = s-pi (raise-value domain) (raise-environment env) body
  raise-value (s-lam domain env body) = s-lam (raise-value domain) (raise-environment env) body
  raise-value (s-neutral head) = s-neutral (raise-neutral head)
  raise-environment : ∀ {d env} → EnvironmentScoped d env → EnvironmentScoped (suc d) env
  raise-environment s[] = s[]
  raise-environment (s∷ head rest) = s∷ (raise-value head) (raise-environment rest)
  raise-neutral : ∀ {d neutral} → NeutralScoped d neutral → NeutralScoped (suc d) neutral
  raise-neutral {d} (s-var inside) = s-var (Nat.<-trans inside (Nat.n<1+n d))
  raise-neutral s-global = s-global
  raise-neutral (s-app function argument) = s-app (raise-neutral function) (raise-value argument)

lookup-scoped : ∀ {d env k value} → EnvironmentScoped d env
  → E.lookup-value env k ≡ just value → ValueScoped d value
lookup-scoped s[] found = ⊥-elim (nothing≠just found)
lookup-scoped {k = zero} (s∷ head rest) found with just-inj found
... | refl = head
lookup-scoped {k = suc k} (s∷ head rest) found = lookup-scoped rest found

mutual
  evaluate-scoped : ∀ {d env term value} → EnvironmentScoped d env → Scoped (length env) term
    → E.Evaluates env term value → ValueScoped d value
  evaluate-scoped env sc-type E.e-type = s-type
  evaluate-scoped env sc-atom_type E.e-atom-type = s-atom-type
  evaluate-scoped env sc-atom_lit E.e-atom = s-atom
  evaluate-scoped env sc-global E.e-global = s-neutral s-global
  evaluate-scoped env (sc-var inside) (E.e-var found) = lookup-scoped env found
  evaluate-scoped env (sc-pi domain body) (E.e-pi evaluated) =
    s-pi (evaluate-scoped env domain evaluated) env body
  evaluate-scoped env (sc-lam domain body) (E.e-lam evaluated) =
    s-lam (evaluate-scoped env domain evaluated) env body
  evaluate-scoped env (sc-app function argument) (E.e-app f a applied) =
    apply-scoped (evaluate-scoped env function f) (evaluate-scoped env argument a) applied
  evaluate-scoped env (sc-let annotation value body) (E.e-let v b) =
    evaluate-scoped (s∷ (evaluate-scoped env value v) env) body b

  apply-scoped : ∀ {d function argument value} → ValueScoped d function → ValueScoped d argument
    → E.Applies function argument value → ValueScoped d value
  apply-scoped (s-lam domain env body) argument (E.a-closure evaluated) =
    evaluate-scoped (s∷ argument env) body evaluated
  apply-scoped (s-neutral function) argument E.a-neutral = s-neutral (s-app function argument)
