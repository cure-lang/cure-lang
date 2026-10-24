{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Checked syntactic callers, not arbitrary semantic environments.
-- Compare OPEN types under fresh slots BEFORE coherent caller closure.
------------------------------------------------------------------------
module Core.ResidualCallerAdmission where

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Core.Syntax
open import Core.Typing using (Ctx; ⟨⟩)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as Source
import Core.CallerAdmission as Caller
import Core.AmbientResidualAdmission as Ambient

record Request : Set where
  constructor request
  field
    caller : Caller.Request
    inferred-kind-recipe : Recipe
checking : Request → Ambient.Request
checking query = Ambient.request (Caller.Request.subject call) (Caller.Request.subject-recipe call)
  (Request.inferred-kind-recipe query) (Caller.Request.goal call) (Caller.Request.goal-recipe call)
  where call = Request.caller query

module Replay {source table certificate-chars}
  (source-checked : Source.Checked source table certificate-chars) where
  module Original = Caller.Replay source-checked
  module Open = Ambient.Replay source-checked
  module C = Original.C
  module D = C.W.G.D
  module N = C.W.N
  module R = C.W.R.R

  record Checked (query : Request) : Set where
    open Caller.Request (Request.caller query)
    field
      size : ℕ
      context : Ctx size
      declaration : N.Declared ⟨⟩ bindings context
      supported-declarations : R.TelescopeSupported 0 bindings
      supported-arguments : R.Terms 0 arguments
      actuals : N.Spine ⟨⟩ [] arguments bindings
      open-checked : Open.Checked context (checking query)
    closure : Original.Checked (Request.caller query)
    closure = record
      { size = size ; context = context ; declaration = declaration
      ; supported-declarations = supported-declarations ; supported-arguments = supported-arguments
      ; actuals = actuals ; supported-subject = Open.Checked.subject-supported open-checked
      ; supported-goal = Open.Checked.goal-supported open-checked
      ; goal-level = Open.Checked.goal-level open-checked ; goal-kind = Open.Checked.goal-kind open-checked
      ; typed = Open.Checked.typed open-checked }
    open Original.Checked closure public using
      (context-valid; substitution; arguments-final; coherent; closed-subject; closed-goal;
       closed-typed; closed-kind; admitted; final; trace-safe; run; tree; budgets-agree)

  verify : ℕ → (query : Request) → Maybe (Checked query)
  verify fuel query with D.declare ⟨⟩ (Caller.Request.bindings (Request.caller query))
    (Caller.Request.kind-recipes (Request.caller query))
  ... | nothing = nothing
  ... | just (size , context , declaration) with R.telescope? 0 (Caller.Request.bindings (Request.caller query))
  ... | no rejected = nothing
  ... | yes supported-declarations with R.terms? 0 (Caller.Request.arguments (Request.caller query))
  ... | no rejected = nothing
  ... | yes supported-arguments with D.spine ⟨⟩ [] (Caller.Request.arguments (Request.caller query))
    (Caller.Request.bindings (Request.caller query)) (Caller.Request.argument-recipes (Request.caller query))
  ... | nothing = nothing
  ... | just actuals with Open.verify-in context (Original.declared-wf N.wf[] declaration) fuel (checking query)
  ... | Ambient.rejected reason = nothing
  ... | Ambient.accepted checked = just record
    { size = size ; context = context ; declaration = declaration
    ; supported-declarations = supported-declarations ; supported-arguments = supported-arguments
    ; actuals = actuals ; open-checked = checked }
