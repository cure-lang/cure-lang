{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Opt-in argument comparison, followed by open checking and coherent
-- caller closure. All recipes are data; expected kinds come from the
-- checked declaration under the already checked prefix.
------------------------------------------------------------------------
module Core.ArgumentCallerAdmission where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst)
open import Core.Syntax
open import Core.Signature using (Telescope)
open import Core.Typing using (Ctx; ⟨⟩)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as Source
import Core.CallerAdmission as Caller
import Core.ResidualCallerAdmission as Residual
import Core.AmbientResidualAdmission as Ambient
import Core.ArgumentAdmission as Argument
import Core.LocalFrame as F

record Request : Set where
  constructor request
  field
    caller : Residual.Request
    argument-kind-recipes : List Recipe

module Replay {source table certificate-chars}
  (source-checked : Source.Checked source table certificate-chars) where
  module A = Argument.Replay source-checked
  module Old = Residual.Replay source-checked
  module C = A.C
  module N = A.N
  module D = A.D
  module R = A.R
  module Frames = A.Frames
  open Argument.ArgumentResults C.W.ind C.W.sig C.W.M.conversion

  -- Requiring both guards here keeps comparison strictly after kinding,
  -- including on the zero-fuel exact branch.
  guarded : ∀ {argument inferred expected i j}
    → N._⊢_⇒_ ⟨⟩ argument inferred
    → N._⊢_⇒_ ⟨⟩ inferred (tm-type i)
    → N._⊢_⇒_ ⟨⟩ expected (tm-type j)
    → R.Supported 0 inferred → R.Supported 0 expected
    → ℕ → Argument.Options → ArgumentResult ⟨⟩ argument expected
  guarded synthesized inferred-kind expected-kind inf-supported exp-supported fuel opts =
    A.compare-argument fuel ⟨⟩ synthesized inf-supported exp-supported opts

  -- No dependent Step index: the recursive result is the existing
  -- CheckedPrefix with the accumulated locals explicitly in its type.
  walk : ∀ {d e} {Δ : Ctx d} {Ε : Ctx e}
    (locals args : List Term) (tele : Telescope)
    → N.Declared Δ tele Ε
    → Frames.Coherent Δ ⟨⟩ (F.prefix locals F.identity)
    → List Recipe → List Recipe → ℕ → Argument.Options
    → Maybe (A.CheckedPrefix ⟨⟩ locals args tele)
  walk locals [] [] N.dt[] coh [] [] fuel opts = just A.cp[]
  walk locals (arg ∷ args) ((name , T) ∷ tele)
    (N.dt∷ {l = level} scoped kind rest) coh (recipe ∷ recipes) (kr ∷ krs) fuel opts
    with R.supported? 0 arg
  ... | no invalid = nothing
  ... | yes arg-supported with D.infer-wf ⟨⟩ N.wf[] arg recipe
  ... | nothing = nothing
  ... | just (inferred , synthesized) with R.supported? 0 inferred
  ... | no invalid = nothing
  ... | yes inf-supported with D.kind-wf ⟨⟩ N.wf[] inferred kr
  ... | nothing = nothing
  ... | just (i , inf-kind) with R.supported? 0 (F.instantiatePrefix locals T)
  ... | no invalid = nothing
  ... | yes exp-supported
    with A.kind-transported T level kind N.wf[] coh
  ... | j , transported
    with A.checked-argument (guarded synthesized inf-kind
      (subst (λ expected → N._⊢_⇒_ ⟨⟩ expected (tm-type j))
        (A.prefix-equal locals T) transported)
      inf-supported exp-supported fuel opts)
  ... | nothing = nothing
  ... | just checked with walk (arg ∷ locals) args tele rest
    (A.prefix-step {locals = locals} {arg = arg} {T = T} (R.final arg-supported) checked coh)
    recipes krs fuel opts
  ... | nothing = nothing
  ... | just tail = just (A.cp∷ (R.final arg-supported) checked tail)
  walk locals args tele declaration coh recipes kinds fuel opts = nothing

  Checked : Request → Set
  Checked query = Old.Checked (Request.caller query)

  verify : ℕ → Argument.Options → (query : Request) → Maybe (Checked query)
  verify fuel opts query with D.declare ⟨⟩
    (Caller.Request.bindings call) (Caller.Request.kind-recipes call)
    where call = Residual.Request.caller (Request.caller query)
  ... | nothing = nothing
  ... | just (size , context , declaration)
    with R.telescope? 0 (Caller.Request.bindings call)
    where call = Residual.Request.caller (Request.caller query)
  ... | no invalid = nothing
  ... | yes declarations with R.terms? 0 (Caller.Request.arguments call)
    where call = Residual.Request.caller (Request.caller query)
  ... | no invalid = nothing
  ... | yes arguments with walk [] (Caller.Request.arguments call)
    (Caller.Request.bindings call) declaration (λ ())
    (Caller.Request.argument-recipes call) (Request.argument-kind-recipes query) fuel opts
    where call = Residual.Request.caller (Request.caller query)
  ... | nothing = nothing
  ... | just prefix with Old.Open.verify-in context
    (Old.Original.declared-wf N.wf[] declaration) fuel (Residual.checking (Request.caller query))
  ... | Ambient.rejected reason = nothing
  ... | Ambient.accepted checked = just record
    { size = size ; context = context ; declaration = declaration
    ; supported-declarations = declarations ; supported-arguments = arguments
    ; actuals = A.prefix-spine prefix ; open-checked = checked }
