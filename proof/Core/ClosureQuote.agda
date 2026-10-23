------------------------------------------------------------------------
-- Positive, height-fuelled Quote MODEL for the closure evaluation slice.
-- Bodies are evaluated under a fresh neutral BEFORE domain/body quote.
-- Beta/zeta normality is not full signature normality (globals remain).
------------------------------------------------------------------------
module Core.ClosureQuote where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _∸_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no)
open import Core.Syntax
import Core.ClosureEval as E
import Core.FlatContext as Flat

mutual
  data Quoted (depth : ℕ) : E.Value → Term → Set where
    q-type : ∀ {l} → Quoted depth (E.v-type l) (tm-type l)
    q-atom-type : Quoted depth E.v-atom-type tm-atom_type
    q-atom : ∀ {name} → Quoted depth (E.v-atom name) (tm-atom_lit name)
    q-ctor : ∀ {name values terms} → SpineQuoted depth values terms
      → Quoted depth (E.v-ctor name values) (tm-ctor name terms)
    q-pi : ∀ {g domain env body value D B}
      → E.Evaluates (E.v-neutral (E.n-var depth) ∷ env) body value
      → Quoted depth domain D → Quoted (suc depth) value B
      → Quoted depth (E.v-pi g domain env body) (tm-pi g D B)
    q-lam : ∀ {g domain env body value D B}
      → E.Evaluates (E.v-neutral (E.n-var depth) ∷ env) body value
      → Quoted depth domain D → Quoted (suc depth) value B
      → Quoted depth (E.v-lam g domain env body) (tm-lam g D B)
    q-neutral : ∀ {head term} → NeutralQuoted depth head term → Quoted depth (E.v-neutral head) term
  data NeutralQuoted (depth : ℕ) : E.Neutral → Term → Set where
    q-var : ∀ {level} → level < depth → NeutralQuoted depth (E.n-var level) (tm-var (depth ∸ suc level))
    q-global : ∀ {name} → NeutralQuoted depth (E.n-global name) (tm-global name)
    q-app : ∀ {function argument f a} → NeutralQuoted depth function f → Quoted depth argument a
      → NeutralQuoted depth (E.n-app function argument) (tm-app f a)
  data SpineQuoted (depth : ℕ) : List E.Value → List Term → Set where
    q[] : SpineQuoted depth [] []
    q∷ : ∀ {value values term terms} → Quoted depth value term → SpineQuoted depth values terms
      → SpineQuoted depth (value ∷ values) (term ∷ terms)

mutual
  run : (fuel depth : ℕ) (value : E.Value) → E.Result (Σ Term (Quoted depth value))
  run zero depth value = E.stop E.exhausted
  run (suc fuel) depth (E.v-type l) = E.done (tm-type l , q-type)
  run (suc fuel) depth E.v-atom-type = E.done (tm-atom_type , q-atom-type)
  run (suc fuel) depth (E.v-atom name) = E.done (tm-atom_lit name , q-atom)
  run (suc fuel) depth (E.v-ctor name values) with spine-run fuel depth values
  ... | E.stop reason = E.stop reason
  ... | E.done (terms , quoted) = E.done (tm-ctor name terms , q-ctor quoted)
  run (suc fuel) depth (E.v-pi g domain env body)
    with E.run fuel body (E.v-neutral (E.n-var depth) ∷ env)
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with run fuel depth domain
  ... | E.stop reason = E.stop reason
  ... | E.done (D , domain-quoted) with run fuel (suc depth) value
  ... | E.stop reason = E.stop reason
  ... | E.done (B , body-quoted) = E.done (tm-pi g D B , q-pi evaluated domain-quoted body-quoted)
  run (suc fuel) depth (E.v-lam g domain env body)
    with E.run fuel body (E.v-neutral (E.n-var depth) ∷ env)
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with run fuel depth domain
  ... | E.stop reason = E.stop reason
  ... | E.done (D , domain-quoted) with run fuel (suc depth) value
  ... | E.stop reason = E.stop reason
  ... | E.done (B , body-quoted) = E.done (tm-lam g D B , q-lam evaluated domain-quoted body-quoted)
  run (suc fuel) depth (E.v-neutral head) with neutral-run fuel depth head
  ... | E.stop reason = E.stop reason
  ... | E.done (term , quoted) = E.done (term , q-neutral quoted)

  neutral-run : (fuel depth : ℕ) (head : E.Neutral) → E.Result (Σ Term (NeutralQuoted depth head))
  neutral-run zero depth head = E.stop E.exhausted
  neutral-run (suc fuel) depth (E.n-var level) with Nat._<?_ level depth
  ... | yes inside = E.done (tm-var (depth ∸ suc level) , q-var inside)
  ... | no outside = E.stop E.escaped-level
  neutral-run (suc fuel) depth (E.n-global name) = E.done (tm-global name , q-global)
  neutral-run (suc fuel) depth (E.n-app function argument) with neutral-run fuel depth function
  ... | E.stop reason = E.stop reason
  ... | E.done (f , function-quoted) with run fuel depth argument
  ... | E.stop reason = E.stop reason
  ... | E.done (a , argument-quoted) = E.done (tm-app f a , q-app function-quoted argument-quoted)

  spine-run : (fuel depth : ℕ) (values : List E.Value) → E.Result (Σ (List Term) (SpineQuoted depth values))
  spine-run zero depth values = E.stop E.exhausted
  spine-run (suc fuel) depth [] = E.done ([] , q[])
  spine-run (suc fuel) depth (value ∷ values) with run fuel depth value
  ... | E.stop reason = E.stop reason
  ... | E.done (term , quoted) with spine-run fuel depth values
  ... | E.stop reason = E.stop reason
  ... | E.done (terms , rest) = E.done (term ∷ terms , q∷ quoted rest)

record Normalizes (depth : ℕ) (env : List E.Value) (term result : Term) : Set where
  constructor normalized
  field
    value : E.Value
    evaluated : E.Evaluates env term value
    quoted : Quoted depth value result
normalise : (fuel depth : ℕ) (term : Term) (env : List E.Value) → E.Result (Σ Term (Normalizes depth env term))
normalise zero depth term env = E.stop E.exhausted
normalise (suc fuel) depth term env with E.run fuel term env
... | E.stop reason = E.stop reason
... | E.done (value , evaluated) with run fuel depth value
... | E.stop reason = E.stop reason
... | E.done (result , quoted) = E.done (result , normalized value evaluated quoted)

mutual
  data BetaZetaNormal : Term → Set where
    normal-type : ∀ {l} → BetaZetaNormal (tm-type l)
    normal-atom-type : BetaZetaNormal tm-atom_type
    normal-atom : ∀ {name} → BetaZetaNormal (tm-atom_lit name)
    normal-ctor : ∀ {name terms} → SpineNormal terms → BetaZetaNormal (tm-ctor name terms)
    normal-pi : ∀ {g D B} → BetaZetaNormal D → BetaZetaNormal B → BetaZetaNormal (tm-pi g D B)
    normal-lam : ∀ {g D B} → BetaZetaNormal D → BetaZetaNormal B → BetaZetaNormal (tm-lam g D B)
    normal-neutral : ∀ {head} → NeutralNormal head → BetaZetaNormal head
  data NeutralNormal : Term → Set where
    normal-var : ∀ {k} → NeutralNormal (tm-var k)
    normal-global : ∀ {name} → NeutralNormal (tm-global name)
    normal-app : ∀ {f a} → NeutralNormal f → BetaZetaNormal a → NeutralNormal (tm-app f a)
  data SpineNormal : List Term → Set where
    normal[] : SpineNormal []
    normal∷ : ∀ {term terms} → BetaZetaNormal term → SpineNormal terms → SpineNormal (term ∷ terms)

mutual
  quoted-normal : ∀ {d value term} → Quoted d value term → BetaZetaNormal term
  quoted-normal q-type = normal-type
  quoted-normal q-atom-type = normal-atom-type
  quoted-normal q-atom = normal-atom
  quoted-normal (q-ctor fields) = normal-ctor (spine-normal fields)
  quoted-normal (q-pi evaluated domain body) = normal-pi (quoted-normal domain) (quoted-normal body)
  quoted-normal (q-lam evaluated domain body) = normal-lam (quoted-normal domain) (quoted-normal body)
  quoted-normal (q-neutral head) = normal-neutral (neutral-normal head)
  neutral-normal : ∀ {d head term} → NeutralQuoted d head term → NeutralNormal term
  neutral-normal (q-var inside) = normal-var
  neutral-normal q-global = normal-global
  neutral-normal (q-app function argument) = normal-app (neutral-normal function) (quoted-normal argument)
  spine-normal : ∀ {d values terms} → SpineQuoted d values terms → SpineNormal terms
  spine-normal q[] = normal[]
  spine-normal (q∷ head rest) = normal∷ (quoted-normal head) (spine-normal rest)

mutual
  quoted-scoped : ∀ {d value term} → Quoted d value term → Scoped d term
  quoted-scoped q-type = sc-type
  quoted-scoped q-atom-type = sc-atom_type
  quoted-scoped q-atom = sc-atom_lit
  quoted-scoped (q-ctor fields) = sc-ctor (spine-scoped fields)
  quoted-scoped (q-pi evaluated domain body) = sc-pi (quoted-scoped domain) (quoted-scoped body)
  quoted-scoped (q-lam evaluated domain body) = sc-lam (quoted-scoped domain) (quoted-scoped body)
  quoted-scoped (q-neutral head) = neutral-scoped head
  neutral-scoped : ∀ {d head term} → NeutralQuoted d head term → Scoped d term
  neutral-scoped {d} (q-var {level} inside) = sc-var (Flat.index-bounded d level inside)
  neutral-scoped q-global = sc-global
  neutral-scoped (q-app function argument) = sc-app (neutral-scoped function) (quoted-scoped argument)
  spine-scoped : ∀ {d values terms} → SpineQuoted d values terms → ScopedTerms d terms
  spine-scoped q[] = st[]
  spine-scoped (q∷ head rest) = st∷ (quoted-scoped head) (spine-scoped rest)
