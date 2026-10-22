------------------------------------------------------------------------
-- Historical size-indexed semantic-value SHAPE, not evaluator refinement.
--
-- This models parts of `Cure.Core.Value`'s shape. It does not establish
-- representation adequacy, Eval/Quote correctness or termination; payload
-- and data-spine discrepancies remain separate obligations.
--
-- Binders are represented by CLOSURES `(env , body)` — an environment plus
-- an unevaluated body. Stuck computations are NEUTRALS carrying a de Bruijn
-- *level* head (read-back converts levels to indices).
--
-- The environment is a `List Value` indexed by de Bruijn index: tm-var 0` is
-- the most-recently-bound variable, at the head of the list.
--
-- The stored environment uses a smaller index, but the body is an
-- ARBITRARY Term: no relation to its syntax size is encoded. A captured
-- body is not necessarily a subterm of the current application, so this
-- index cannot justify evaluator recursion or totality. Core.ClosureEval
-- instead exposes a structurally fuelled positive evaluation model.
------------------------------------------------------------------------
module Core.Value where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax using (Term; Branch; Name; ℤ′; shift)

------------------------------------------------------------------------
-- An index constrains nested captured environments, not originating term
-- sizes or evaluation work. No evaluator is defined by this datatype.
------------------------------------------------------------------------

mutual
  data Val (n : ℕ) : Set where
    vtype    : Level → Val n
    vpi      : Grade → Val n → Clo n → Val n
    vlam     : Grade → Val n → Clo n → Val n
    vneutral : Neutral n → Val n
    vdata    : Name → List (Val n) → Val n
    vctor    : Name → List (Val n) → Val n
    vint_type    : Val n
    vint         : ℤ′ → Val n
    vnat         : ℕ → Val n
    vbounded     : ℕ → Val n
    vfloat_type  : Val n
    vfloat       : Val n
    vbinary_type : Val n
    vatom_type   : Val n
    vatom        : Name → Val n
    veffect_type : Val n → Val n
    veffect_pure : Val n → Val n
    veffect_bind : Val n → Val n → Val n

  -- A closure: an environment plus an unevaluated body term. The captured
  -- environment is drawn from a smaller index; the unindexed body term
  -- carries no termination or syntax-size proof.
  Clo : ℕ → Set
  Clo n = Σ ℕ (λ m → m < n × List (Val m) × Term)

  -- A stuck computation: a head plus an eliminator spine.
  data Neutral (n : ℕ) : Set where
    nvar    : ℕ → Neutral n
    nglobal : Name → Neutral n
    nhole   : Name → Neutral n
    napp    : Neutral n → Val n → Neutral n
    ncase   : Neutral n → Clo n → List (BranchClo n) → Neutral n

  -- A `:ncase` branch closure: constructor name, arity, and the branch closure.
  data BranchClo (n : ℕ) : Set where
    bclo : Name → ℕ → Clo n → BranchClo n

------------------------------------------------------------------------
-- Environments
--
-- An environment is a list of values, all drawn from the same bound `n`.
------------------------------------------------------------------------

Env : ℕ → Set
Env n = List (Val n)
