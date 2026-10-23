------------------------------------------------------------------------
-- Positive exact-arity case MODEL simulation for arbitrary signatures.
-- The caller tail and all field binders are substituted simultaneously.
------------------------------------------------------------------------
module Proof.ClosureCase where

open import Data.List using (List; []; _∷_; _++_; reverse; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Reduction using (Signature; _⇝*_; ⇝*-refl; ⇝*-step; ι; argsSub;
  substArgs; findBranch-substBranchesS; findBranch; findBranch-sound)
import Core.ClosureEval as E
import Core.ClosureCase as C
import Core.LocalFrame as F
import Proof.ClosureEvaluation as M
import Proof.ClosureFrame as Frame
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Proof.ClosureQuotation as Quote

fields-scoped : ∀ {d env args values} → Scope.EnvironmentScoped d env
  → ScopedTerms (length env) args → C.Fields env args values → Scope.EnvironmentScoped d values
fields-scoped env terms fields = Scope.spine-scoped env terms (C.fields-evaluated fields)

append-scoped : ∀ {d vs ws} → Scope.EnvironmentScoped d vs → Scope.EnvironmentScoped d ws
  → Scope.EnvironmentScoped d (vs ++ ws)
append-scoped = Scope.append-scoped

reverse-scoped : ∀ {d vs} → Scope.EnvironmentScoped d vs → Scope.EnvironmentScoped d (reverse vs)
reverse-scoped = Scope.reverse-scoped

selected-scope : ∀ {d name ar body branches} → ScopedBranches d branches
  → findBranch name branches ≡ just (name , ar , body) → Scoped (d Data.Nat.+ ar) body
selected-scope = Scope.selected-scope

evaluate-scoped : ∀ {d env term value} → Scope.EnvironmentScoped d env
  → Scoped (length env) term → C.Executes env term value → Scope.ValueScoped d value
evaluate-scoped scope scoped execution = Scope.evaluate-scoped scope scoped (C.to-shared execution)

environment-length : ∀ {d values terms} → M.Environments d values terms → length terms ≡ length values
environment-length = M.environment-length

append-environments : ∀ {d vs ts ws us} → M.Environments d vs ts → M.Environments d ws us
  → M.Environments d (vs ++ ws) (ts ++ us)
append-environments = M.append-environments

reverse-environments : ∀ {d vs ts} → M.Environments d vs ts → M.Environments d (reverse vs) (reverse ts)
reverse-environments = M.reverse-environments

consume : ∀ xs σ k → substS (argsSub xs) (extSub^ (length xs) σ k) ≡ F.prefix xs σ k
consume = Frame.consume

-- No scope premise is needed: both substitutions retain the same caller
-- tail even on arbitrary raw bodies and beneath their nested binders.
branch-environment : ∀ args terms body
  → substArgs args (substS (extSub^ (length args) (M.environment-sub terms)) body)
    ≡ substS (M.environment-sub (reverse args ++ terms)) body
branch-environment = Frame.branch-environment

module Simulation (sig : Signature) where
  module Eval = M.Simulation sig
  module O = Eval.O

  -- Return the denotation vector and its constructor congruence path.
  fields : ∀ {d env terms args values} → M.Environments d env terms → C.Fields env args values
    → ∃ λ results → M.Environments d values results ×
      (∀ name → _⇝*_ sig (tm-ctor name (substTermsS (M.environment-sub terms) args)) (tm-ctor name results))
  fields env evaluated = Eval.spine env (C.fields-evaluated evaluated)

  evaluate : ∀ {d env terms term value} → M.Environments d env terms → C.Executes env term value
    → ∃ λ result → M.Denotes d value result × _⇝*_ sig (substS (M.environment-sub terms) term) result
  evaluate env execution = Eval.evaluate env (C.to-shared execution)

  module Quotation = Quote.Simulation sig
  quotation : ∀ {d env terms term value quoted}
    → Scope.EnvironmentScoped d env → Scoped (length env) term → M.Environments d env terms
    → C.Executes env term value → Q.Quoted d value quoted
    → _⇝*_ sig (substS (M.environment-sub terms) term) quoted
  quotation scope scoped env execution quoted with evaluate env execution
  ... | result , denoted , path = O.⇝*-trans path
    (Quotation.quotation (evaluate-scoped scope scoped execution) denoted quoted)

