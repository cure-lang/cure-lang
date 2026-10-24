------------------------------------------------------------------------
-- Positive, height-fuelled Quote MODEL for the closure evaluation slice.
-- Bodies are evaluated under a fresh neutral BEFORE domain/body quote.
-- Explicit signature mode follows captured bodies and validates data splits.
-- Beta/zeta normality is not full signature normality (globals remain).
-- Residual permission is separate from signature mode and from typing.
------------------------------------------------------------------------
module Core.ClosureQuote where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; _+_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Core.Signature using (IndEnv)
import Core.DataSpine as Layout
open import Relation.Nullary using (yes; no)
open import Core.Syntax
import Core.ClosureEval as E
import Core.FlatContext as Flat
import Core.BranchOpening as Opening

mutual
  data QuotedIn (residual : Bool) (depth : ℕ) : E.Value → Term → Set where
    q-type : ∀ {l} → QuotedIn residual depth (E.v-type l) (tm-type l)
    q-atom-type : QuotedIn residual depth E.v-atom-type tm-atom_type
    q-atom : ∀ {name} → QuotedIn residual depth (E.v-atom name) (tm-atom_lit name)
    q-ctor : ∀ {name values terms} → SpineQuotedIn residual depth values terms
      → QuotedIn residual depth (E.v-ctor name values) (tm-ctor name terms)
    q-data : ∀ {name pvs ivs ps is} → SpineQuotedIn residual depth pvs ps → SpineQuotedIn residual depth ivs is
      → QuotedIn residual depth (E.v-data name pvs ivs) (tm-data name ps is)
    q-pi : ∀ {g domain env body value D B}
      → E.Evaluates (E.v-neutral (E.n-var depth) ∷ env) body value
      → QuotedIn residual depth domain D → QuotedIn residual (suc depth) value B
      → QuotedIn residual depth (E.v-pi g domain env body) (tm-pi g D B)
    q-lam : ∀ {g domain env body value D B}
      → E.Evaluates (E.v-neutral (E.n-var depth) ∷ env) body value
      → QuotedIn residual depth domain D → QuotedIn residual (suc depth) value B
      → QuotedIn residual depth (E.v-lam g domain env body) (tm-lam g D B)
    q-neutral : ∀ {head term} → NeutralQuotedIn residual depth head term → QuotedIn residual depth (E.v-neutral head) term
  data NeutralQuotedIn (residual : Bool) (depth : ℕ) : E.Neutral → Term → Set where
    q-var : ∀ {level} → level < depth → NeutralQuotedIn residual depth (E.n-var level) (tm-var (depth ∸ suc level))
    q-global : ∀ {name} → NeutralQuotedIn residual depth (E.n-global name) (tm-global name)
    q-app : ∀ {function argument f a} → NeutralQuotedIn residual depth function f → QuotedIn residual depth argument a
      → NeutralQuotedIn residual depth (E.n-app function argument) (tm-app f a)
    q-case : ∀ {head env motive branches s m results value}
      → residual ≡ true → NeutralQuotedIn residual depth head s
      → E.Evaluates env motive value → QuotedIn residual depth value m
      → BranchesQuotedIn residual depth env branches results
      → NeutralQuotedIn residual depth (E.n-case head env motive branches) (tm-case s m results)
  data SpineQuotedIn (residual : Bool) (depth : ℕ) : List E.Value → List Term → Set where
    q[] : SpineQuotedIn residual depth [] []
    q∷ : ∀ {value values term terms} → QuotedIn residual depth value term → SpineQuotedIn residual depth values terms
      → SpineQuotedIn residual depth (value ∷ values) (term ∷ terms)
  data BranchesQuotedIn (residual : Bool) (depth : ℕ) (env : List E.Value) : List Branch → List Branch → Set where
    qb[] : BranchesQuotedIn residual depth env [] []
    qb∷ : ∀ {name ar body rest term terms value}
      → E.Evaluates (Opening.environment depth ar env) body value
      → QuotedIn residual (ar + depth) value term → BranchesQuotedIn residual depth env rest terms
      → BranchesQuotedIn residual depth env ((name , ar , body) ∷ rest) ((name , ar , term) ∷ terms)

-- Strict evidence is the residual-disabled specialization; no case can inhabit it.
Quoted : ℕ → E.Value → Term → Set
Quoted = QuotedIn false
NeutralQuoted : ℕ → E.Neutral → Term → Set
NeutralQuoted = NeutralQuotedIn false
SpineQuoted : ℕ → List E.Value → List Term → Set
SpineQuoted = SpineQuotedIn false

spine-length : ∀ {depth values terms} → SpineQuoted depth values terms → length terms ≡ length values
spine-length q[] = refl
spine-length (q∷ head rest) = cong suc (spine-length rest)
quoted-layout : ∀ {ind name depth pvs ivs ps is} → Layout.SourceLayout ind name pvs ivs
  → SpineQuoted depth pvs ps → SpineQuoted depth ivs is → Layout.SourceLayout ind name ps is
quoted-layout layout params indices = Layout.source-layout
  (Layout.SourceLayout.family layout) (Layout.SourceLayout.found layout)
  (trans (spine-length params) (Layout.SourceLayout.parameter-count layout))
  (trans (spine-length indices) (Layout.SourceLayout.index-count layout))

mutual
  run-config : (residual : Bool) → (mode : Maybe IndEnv) → (fuel depth : ℕ) (value : E.Value) → E.Result (Σ Term (QuotedIn residual depth value))
  run-config residual mode zero depth value = E.stop E.exhausted
  run-config residual mode (suc fuel) depth (E.v-type l) = E.done (tm-type l , q-type)
  run-config residual mode (suc fuel) depth E.v-atom-type = E.done (tm-atom_type , q-atom-type)
  run-config residual mode (suc fuel) depth (E.v-atom name) = E.done (tm-atom_lit name , q-atom)
  run-config residual mode (suc fuel) depth (E.v-ctor name values) with spine-config residual mode fuel depth values
  ... | E.stop reason = E.stop reason
  ... | E.done (terms , quoted) = E.done (tm-ctor name terms , q-ctor quoted)
  run-config residual nothing (suc fuel) depth (E.v-data name pvs ivs) = E.stop E.unsupported
  run-config residual (just ind) (suc fuel) depth (E.v-data name pvs ivs) with Layout.check-source ind name pvs ivs
  ... | Layout.rejected reason = E.stop (E.data-layout reason)
  ... | Layout.accepted layout with spine-config residual (just ind) fuel depth pvs
  ... | E.stop reason = E.stop reason
  ... | E.done (ps , params) with spine-config residual (just ind) fuel depth ivs
  ... | E.stop reason = E.stop reason
  ... | E.done (is , indices) = E.done (tm-data name ps is , q-data params indices)
  run-config residual mode (suc fuel) depth (E.v-pi g domain env body)
    with E.run-config residual mode fuel body (E.v-neutral (E.n-var depth) ∷ env)
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with run-config residual mode fuel depth domain
  ... | E.stop reason = E.stop reason
  ... | E.done (D , domain-quoted) with run-config residual mode fuel (suc depth) value
  ... | E.stop reason = E.stop reason
  ... | E.done (B , body-quoted) = E.done (tm-pi g D B , q-pi evaluated domain-quoted body-quoted)
  run-config residual mode (suc fuel) depth (E.v-lam g domain env body)
    with E.run-config residual mode fuel body (E.v-neutral (E.n-var depth) ∷ env)
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with run-config residual mode fuel depth domain
  ... | E.stop reason = E.stop reason
  ... | E.done (D , domain-quoted) with run-config residual mode fuel (suc depth) value
  ... | E.stop reason = E.stop reason
  ... | E.done (B , body-quoted) = E.done (tm-lam g D B , q-lam evaluated domain-quoted body-quoted)
  run-config residual mode (suc fuel) depth (E.v-neutral head) with neutral-config residual mode fuel depth head
  ... | E.stop reason = E.stop reason
  ... | E.done (term , quoted) = E.done (term , q-neutral quoted)

  neutral-config : (residual : Bool) → (mode : Maybe IndEnv) → (fuel depth : ℕ) (head : E.Neutral) → E.Result (Σ Term (NeutralQuotedIn residual depth head))
  neutral-config residual mode zero depth head = E.stop E.exhausted
  neutral-config residual mode (suc fuel) depth (E.n-var level) with Nat._<?_ level depth
  ... | yes inside = E.done (tm-var (depth ∸ suc level) , q-var inside)
  ... | no outside = E.stop E.escaped-level
  neutral-config residual mode (suc fuel) depth (E.n-global name) = E.done (tm-global name , q-global)
  neutral-config residual mode (suc fuel) depth (E.n-app function argument) with neutral-config residual mode fuel depth function
  ... | E.stop reason = E.stop reason
  ... | E.done (f , function-quoted) with run-config residual mode fuel depth argument
  ... | E.stop reason = E.stop reason
  ... | E.done (a , argument-quoted) = E.done (tm-app f a , q-app function-quoted argument-quoted)
  neutral-config false mode (suc fuel) depth (E.n-case head env motive branches) = E.stop E.neutral-scrutinee
  neutral-config true mode (suc fuel) depth (E.n-case head env motive branches)
    with neutral-config true mode fuel depth head
  ... | E.stop reason = E.stop reason
  ... | E.done (s , head-quoted) with E.run-residual-in mode fuel motive env
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with run-config true mode fuel depth value
  ... | E.stop reason = E.stop reason
  ... | E.done (m , motive-quoted) with branches-config true mode fuel depth env branches
  ... | E.stop reason = E.stop reason
  ... | E.done (results , bodies) = E.done (tm-case s m results , q-case refl head-quoted evaluated motive-quoted bodies)

  spine-config : (residual : Bool) → (mode : Maybe IndEnv) → (fuel depth : ℕ) (values : List E.Value) → E.Result (Σ (List Term) (SpineQuotedIn residual depth values))
  spine-config residual mode zero depth values = E.stop E.exhausted
  spine-config residual mode (suc fuel) depth [] = E.done ([] , q[])
  spine-config residual mode (suc fuel) depth (value ∷ values) with run-config residual mode fuel depth value
  ... | E.stop reason = E.stop reason
  ... | E.done (term , quoted) with spine-config residual mode fuel depth values
  ... | E.stop reason = E.stop reason
  ... | E.done (terms , rest) = E.done (term ∷ terms , q∷ quoted rest)

  branches-config : (residual : Bool) → Maybe IndEnv → (fuel depth : ℕ) (env : List E.Value) (branches : List Branch)
    → E.Result (Σ (List Branch) (BranchesQuotedIn residual depth env branches))
  branches-config residual mode zero depth env branches = E.stop E.exhausted
  branches-config residual mode (suc fuel) depth env [] = E.done ([] , qb[])
  branches-config residual mode (suc fuel) depth env ((name , ar , body) ∷ rest)
    with E.run-config residual mode fuel body (Opening.environment depth ar env)
  ... | E.stop reason = E.stop reason
  ... | E.done (value , evaluated) with run-config residual mode fuel (ar + depth) value
  ... | E.stop reason = E.stop reason
  ... | E.done (term , quoted) with branches-config residual mode fuel depth env rest
  ... | E.stop reason = E.stop reason
  ... | E.done (terms , tail) = E.done ((name , ar , term) ∷ terms , qb∷ evaluated quoted tail)

run-in : Maybe IndEnv → (fuel depth : ℕ) (value : E.Value) → E.Result (Σ Term (Quoted depth value))
run-in = run-config false
neutral-run-in : Maybe IndEnv → (fuel depth : ℕ) (head : E.Neutral) → E.Result (Σ Term (NeutralQuoted depth head))
neutral-run-in = neutral-config false
spine-run-in : Maybe IndEnv → (fuel depth : ℕ) (values : List E.Value) → E.Result (Σ (List Term) (SpineQuoted depth values))
spine-run-in = spine-config false

run : (fuel depth : ℕ) (value : E.Value) → E.Result (Σ Term (Quoted depth value))
run = run-in nothing
neutral-run : (fuel depth : ℕ) (head : E.Neutral) → E.Result (Σ Term (NeutralQuoted depth head))
neutral-run = neutral-run-in nothing
spine-run : (fuel depth : ℕ) (values : List E.Value) → E.Result (Σ (List Term) (SpineQuoted depth values))
spine-run = spine-run-in nothing
run-with : IndEnv → (fuel depth : ℕ) (value : E.Value) → E.Result (Σ Term (Quoted depth value))
run-with ind = run-in (just ind)
spine-run-with : IndEnv → (fuel depth : ℕ) (values : List E.Value)
  → E.Result (Σ (List Term) (SpineQuoted depth values))
spine-run-with ind = spine-run-in (just ind)

record Normalizes (depth : ℕ) (env : List E.Value) (term result : Term) : Set where
  constructor normalized
  field
    value : E.Value
    evaluated : E.Evaluates env term value
    quoted : Quoted depth value result
normalise-in : Maybe IndEnv → (fuel depth : ℕ) (term : Term) (env : List E.Value)
  → E.Result (Σ Term (Normalizes depth env term))
normalise-in mode zero depth term env = E.stop E.exhausted
normalise-in mode (suc fuel) depth term env with E.run-in mode fuel term env
... | E.stop reason = E.stop reason
... | E.done (value , evaluated) with run-in mode fuel depth value
... | E.stop reason = E.stop reason
... | E.done (result , quoted) = E.done (result , normalized value evaluated quoted)
normalise : (fuel depth : ℕ) (term : Term) (env : List E.Value) → E.Result (Σ Term (Normalizes depth env term))
normalise = normalise-in nothing
normalise-with : IndEnv → (fuel depth : ℕ) (term : Term) (env : List E.Value)
  → E.Result (Σ Term (Normalizes depth env term))
normalise-with ind = normalise-in (just ind)

-- Residual forms have their OWN positive contract; strict no-step is not claimed.
record ResidualNormalizes (depth : ℕ) (env : List E.Value) (term result : Term) : Set where
  constructor residual-normalized
  field
    value : E.Value
    evaluated : E.Evaluates env term value
    quoted : QuotedIn true depth value result
normalise-residual-in : Maybe IndEnv → (fuel depth : ℕ) (term : Term) (env : List E.Value)
  → E.Result (Σ Term (ResidualNormalizes depth env term))
normalise-residual-in mode zero depth term env = E.stop E.exhausted
normalise-residual-in mode (suc fuel) depth term env with E.run-residual-in mode fuel term env
... | E.stop reason = E.stop reason
... | E.done (value , evaluated) with run-config true mode fuel depth value
... | E.stop reason = E.stop reason
... | E.done (result , quoted) = E.done (result , residual-normalized value evaluated quoted)
normalise-residual : (fuel depth : ℕ) (term : Term) (env : List E.Value)
  → E.Result (Σ Term (ResidualNormalizes depth env term))
normalise-residual = normalise-residual-in nothing
normalise-residual-with : IndEnv → (fuel depth : ℕ) (term : Term) (env : List E.Value)
  → E.Result (Σ Term (ResidualNormalizes depth env term))
normalise-residual-with ind = normalise-residual-in (just ind)

mutual
  data BetaZetaNormal : Term → Set where
    normal-type : ∀ {l} → BetaZetaNormal (tm-type l)
    normal-atom-type : BetaZetaNormal tm-atom_type
    normal-atom : ∀ {name} → BetaZetaNormal (tm-atom_lit name)
    normal-ctor : ∀ {name terms} → SpineNormal terms → BetaZetaNormal (tm-ctor name terms)
    normal-data : ∀ {name ps is} → SpineNormal ps → SpineNormal is → BetaZetaNormal (tm-data name ps is)
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
  quoted-normal (q-data params indices) = normal-data (spine-normal params) (spine-normal indices)
  quoted-normal (q-pi evaluated domain body) = normal-pi (quoted-normal domain) (quoted-normal body)
  quoted-normal (q-lam evaluated domain body) = normal-lam (quoted-normal domain) (quoted-normal body)
  quoted-normal (q-neutral head) = normal-neutral (neutral-normal head)
  neutral-normal : ∀ {d head term} → NeutralQuoted d head term → NeutralNormal term
  neutral-normal (q-var inside) = normal-var
  neutral-normal q-global = normal-global
  neutral-normal (q-app function argument) = normal-app (neutral-normal function) (quoted-normal argument)
  neutral-normal (q-case () head evaluated motive branches)
  spine-normal : ∀ {d values terms} → SpineQuoted d values terms → SpineNormal terms
  spine-normal q[] = normal[]
  spine-normal (q∷ head rest) = normal∷ (quoted-normal head) (spine-normal rest)

mutual
  quoted-scoped : ∀ {d value term residual} → QuotedIn residual d value term → Scoped d term
  quoted-scoped q-type = sc-type
  quoted-scoped q-atom-type = sc-atom_type
  quoted-scoped q-atom = sc-atom_lit
  quoted-scoped (q-ctor fields) = sc-ctor (spine-scoped fields)
  quoted-scoped (q-data params indices) = sc-data (spine-scoped params) (spine-scoped indices)
  quoted-scoped (q-pi evaluated domain body) = sc-pi (quoted-scoped domain) (quoted-scoped body)
  quoted-scoped (q-lam evaluated domain body) = sc-lam (quoted-scoped domain) (quoted-scoped body)
  quoted-scoped (q-neutral head) = neutral-scoped head
  neutral-scoped : ∀ {d head term residual} → NeutralQuotedIn residual d head term → Scoped d term
  neutral-scoped {d = d} (q-var {level} inside) = sc-var (Flat.index-bounded d level inside)
  neutral-scoped q-global = sc-global
  neutral-scoped (q-app function argument) = sc-app (neutral-scoped function) (quoted-scoped argument)
  neutral-scoped (q-case allowed head evaluated motive branches) =
    sc-case (neutral-scoped head) (quoted-scoped motive) (branches-scoped branches)
  branches-scoped : ∀ {residual d env source results} → BranchesQuotedIn residual d env source results → ScopedBranches d results
  branches-scoped qb[] = sb[]
  branches-scoped {d = d} (qb∷ {ar = ar} {term = term} evaluated quoted tail) = sb∷
    (sbranch (Relation.Binary.PropositionalEquality.subst (λ n → Scoped n term) (Nat.+-comm ar d)
      (quoted-scoped quoted))) (branches-scoped tail)
  spine-scoped : ∀ {d values terms residual} → SpineQuotedIn residual d values terms → ScopedTerms d terms
  spine-scoped q[] = st[]
  spine-scoped (q∷ head rest) = st∷ (quoted-scoped head) (spine-scoped rest)
