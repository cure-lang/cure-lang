------------------------------------------------------------------------
-- Positive exact-arity case MODEL simulation for arbitrary signatures.
-- The caller tail and all field binders are substituted simultaneously.
------------------------------------------------------------------------
module Proof.ClosureCase where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.List.Properties using (unfold-reverse; length-reverse; length-++)
open import Data.Nat using (ℕ; zero; suc)
import Data.Fin
import Data.Nat.Properties as Nat
open import Data.Maybe using (just)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Reduction using (Signature; _⇝*_; ⇝*-refl; ⇝*-step; ι; argsSub;
  substArgs; findBranch-substBranchesS; findBranch; findBranch-sound)
import Core.ClosureEval as E
import Core.ClosureCase as C
import Core.LocalFrame as F
import Proof.ClosureEvaluation as M
import Proof.Substitution as S
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Proof.ClosureQuotation as Quote

fields-scoped : ∀ {d env args values} → Scope.EnvironmentScoped d env
  → ScopedTerms (length env) args → C.Fields env args values → Scope.EnvironmentScoped d values
fields-scoped env st[] C.f[] = Scope.s[]
fields-scoped env (st∷ head rest) (C.f∷ evaluated evaluations) =
  Scope.s∷ (Scope.evaluate-scoped env head evaluated) (fields-scoped env rest evaluations)

append-scoped : ∀ {d vs ws} → Scope.EnvironmentScoped d vs → Scope.EnvironmentScoped d ws
  → Scope.EnvironmentScoped d (vs ++ ws)
append-scoped Scope.s[] right = right
append-scoped (Scope.s∷ head rest) right = Scope.s∷ head (append-scoped rest right)

reverse-scoped : ∀ {d vs} → Scope.EnvironmentScoped d vs → Scope.EnvironmentScoped d (reverse vs)
reverse-scoped Scope.s[] = Scope.s[]
reverse-scoped (Scope.s∷ {value = v} {env = vs} head rest) =
  subst (Scope.EnvironmentScoped _) (sym (unfold-reverse v vs))
    (append-scoped (reverse-scoped rest) (Scope.s∷ head Scope.s[]))

selected-scope : ∀ {d name ar body branches} → ScopedBranches d branches
  → findBranch name branches ≡ just (name , ar , body) → Scoped (d Data.Nat.+ ar) body
selected-scope scopes found = member scopes (findBranch-sound _ _ found)
  where
    member : ∀ {d name ar body branches} → ScopedBranches d branches
      → (name , ar , body) ∈ branches → Scoped (d Data.Nat.+ ar) body
    member (sb∷ (sbranch body) rest) (here refl) = body
    member (sb∷ head rest) (there inside) = member rest inside

evaluate-scoped : ∀ {d env term value} → Scope.EnvironmentScoped d env
  → Scoped (length env) term → C.Executes env term value → Scope.ValueScoped d value
evaluate-scoped {env = env} scoped (sc-case (sc-ctor args) motive branches)
  (C.executed {ar = ar} {body = body} {values = values} fields found exact evaluated) =
  Scope.evaluate-scoped (append-scoped (reverse-scoped (fields-scoped scoped args fields)) scoped)
    (subst (λ n → Scoped n body) (sym frame-length) (selected-scope branches found)) evaluated
  where
    frame-length : length (reverse values ++ env) ≡ length env Data.Nat.+ ar
    frame-length = trans (length-++ (reverse values))
      (trans (cong (Data.Nat._+ length env) (trans (length-reverse values)
        (trans (C.fields-length fields) exact))) (Nat.+-comm ar (length env)))
evaluate-scoped {env = env} scoped (sc-case scrutinee motive branches)
  (C.computed {ar = ar} {body = body} {values = values} evaluated found exact body-evaluated)
  with Scope.evaluate-scoped scoped scrutinee evaluated
... | Scope.s-ctor fields = Scope.evaluate-scoped
  (append-scoped (reverse-scoped fields) scoped)
  (subst (λ n → Scoped n body) (sym frame-length) (selected-scope branches found)) body-evaluated
  where
    frame-length : length (reverse values ++ env) ≡ length env Data.Nat.+ ar
    frame-length = trans (length-++ (reverse values))
      (trans (cong (Data.Nat._+ length env) (trans (length-reverse values) exact))
        (Nat.+-comm ar (length env)))

environment-length : ∀ {d values terms} → M.Environments d values terms → length terms ≡ length values
environment-length M.d[] = refl
environment-length (M.d∷ head rest) = cong suc (environment-length rest)

append-environments : ∀ {d vs ts ws us} → M.Environments d vs ts → M.Environments d ws us
  → M.Environments d (vs ++ ws) (ts ++ us)
append-environments M.d[] right = right
append-environments (M.d∷ head rest) right = M.d∷ head (append-environments rest right)

reverse-environments : ∀ {d vs ts} → M.Environments d vs ts → M.Environments d (reverse vs) (reverse ts)
reverse-environments M.d[] = M.d[]
reverse-environments (M.d∷ {value = v} {term = t} {env = vs} {terms = ts} head rest) =
  subst (λ xs → M.Environments _ xs (reverse (t ∷ ts))) (sym (unfold-reverse v vs))
    (subst (M.Environments _ (reverse vs ++ v ∷ [])) (sym (unfold-reverse t ts))
      (append-environments (reverse-environments rest) (M.d∷ head M.d[])))

consume : ∀ xs σ k → substS (argsSub xs) (extSub^ (length xs) σ k) ≡ F.prefix xs σ k
consume [] σ k = S.substS-idSub (σ k)
consume (x ∷ xs) σ zero = refl
consume (x ∷ xs) σ (suc k) =
  trans (S.substS-argsSub-wk x xs (extSub^ (length xs) σ k)) (consume xs σ k)

-- No scope premise is needed: both substitutions retain the same caller
-- tail even on arbitrary raw bodies and beneath their nested binders.
branch-environment : ∀ args terms body
  → substArgs args (substS (extSub^ (length args) (M.environment-sub terms)) body)
    ≡ substS (M.environment-sub (reverse args ++ terms)) body
branch-environment args terms body =
  trans (cong (λ n → substS (argsSub (reverse args))
    (substS (extSub^ n (M.environment-sub terms)) body)) (sym (length-reverse args)))
    (trans (S.subst-compose (argsSub (reverse args))
      (extSub^ (length (reverse args)) (M.environment-sub terms)) body)
      (cong (λ σ → substS σ body) (funext (λ k →
        trans (consume (reverse args) (M.environment-sub terms) k)
          (sym (F.prefix-append (reverse args) terms F.identity k))))))

module Simulation (sig : Signature) where
  module Eval = M.Simulation sig
  module O = Eval.O

  -- Return the denotation vector and its constructor congruence path.
  fields : ∀ {d env terms args values} → M.Environments d env terms → C.Fields env args values
    → ∃ λ results → M.Environments d values results ×
      (∀ name → _⇝*_ sig (tm-ctor name (substTermsS (M.environment-sub terms) args)) (tm-ctor name results))
  fields env C.f[] = [] , M.d[] , λ name → ⇝*-refl
  fields env (C.f∷ head rest) with Eval.evaluate env head | fields env rest
  ... | term , denoted , path | terms , environment , paths =
    term ∷ terms , M.d∷ denoted environment , λ name →
      O.⇝*-trans (O.⇝*-at-ctor _ Data.Fin.zero path) (O.⇝*-ctor-tail-shift term (paths name))

  evaluate : ∀ {d env terms term value} → M.Environments d env terms → C.Executes env term value
    → ∃ λ result → M.Denotes d value result × _⇝*_ sig (substS (M.environment-sub terms) term) result
  evaluate {terms = caller} env
    (C.executed {name} {args} {motive} {branches} {ar} {body} evaluated found exact body-evaluated)
    with fields env evaluated
  ... | results , denoted , paths
    with Eval.evaluate (append-environments (reverse-environments denoted) env) body-evaluated
  ... | result , value-denoted , body-path = result , value-denoted ,
    O.⇝*-trans (O.⇝*-case (paths name))
      (⇝*-step (ι (findBranch-substBranchesS (M.environment-sub caller) name branches found) result-arity)
        (O.⇝*-trans (Eval.equal-path frame) body-path))
    where
      result-length : length results ≡ length args
      result-length = trans (environment-length denoted) (C.fields-length evaluated)
      result-arity : length results ≡ ar
      result-arity = trans result-length exact
      frame : substArgs results (substS (extSub^ ar (M.environment-sub caller)) body)
        ≡ substS (M.environment-sub (reverse results ++ caller)) body
      frame = trans (cong (λ n → substArgs results (substS (extSub^ n (M.environment-sub caller)) body))
        (sym result-arity)) (branch-environment results caller body)
  evaluate {terms = caller} env
    (C.computed {branches = branches} {ar = ar} {body = body} evaluated found exact body-evaluated)
    with Eval.evaluate env evaluated
  ... | tm-ctor name results , M.d-ctor fields , scrutinee-path
    with Eval.evaluate (append-environments (reverse-environments fields) env) body-evaluated
  ... | result , value-denoted , body-path = result , value-denoted ,
    O.⇝*-trans (O.⇝*-case scrutinee-path)
      (⇝*-step (ι (findBranch-substBranchesS (M.environment-sub caller) name branches found) result-arity)
        (O.⇝*-trans (Eval.equal-path frame) body-path))
    where
      result-arity : length results ≡ ar
      result-arity = trans (environment-length fields) exact
      frame : substArgs results (substS (extSub^ ar (M.environment-sub caller)) body)
        ≡ substS (M.environment-sub (reverse results ++ caller)) body
      frame = trans (cong (λ n → substArgs results (substS (extSub^ n (M.environment-sub caller)) body))
        (sym result-arity)) (branch-environment results caller body)

  module Quotation = Quote.Simulation sig
  quotation : ∀ {d env terms term value quoted}
    → Scope.EnvironmentScoped d env → Scoped (length env) term → M.Environments d env terms
    → C.Executes env term value → Q.Quoted d value quoted
    → _⇝*_ sig (substS (M.environment-sub terms) term) quoted
  quotation scope scoped env execution quoted with evaluate env execution
  ... | result , denoted , path = O.⇝*-trans path
    (Quotation.quotation (evaluate-scoped scope scoped execution) denoted quoted)

