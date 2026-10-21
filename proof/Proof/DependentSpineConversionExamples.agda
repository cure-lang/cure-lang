------------------------------------------------------------------------
-- Computed result syntax, changed local prefixes, and changed motives.
-- Every typing premise is in the same native E.T judgment.
------------------------------------------------------------------------
module Proof.DependentSpineConversionExamples where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; length)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l1)
open import Core.Signature using (ctor-indices)
open import Core.Reduction using (ζ)
open import Core.Typing using (⟨⟩; Conversion; All2; a2[]; a2∷)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentSpineConversion as ConversionLaws

open E.T
open Conversion
module L = ConversionLaws.Laws E.env E.sig E.conv

wrap : Term → Term
wrap t = tm-let unrestricted (tm-type l1) t (tm-var 0)

ps ps′ fields′ : Data.List.List Term
ps = tm-atom_type ∷ []
ps′ = wrap tm-atom_type ∷ []
fields′ = wrap (tm-atom_lit "payload") ∷ tm-float_type ∷ tm-float_lit ∷ []

abstract
  expanded : ∀ t → _≈_ E.conv t (wrap t)
  expanded t = ≈-sym E.conv {t = wrap t} {u = t}
    (E.R.reduce-converts {t = wrap t} {u = t} ζ)

  pars-convertible : All2 (_≈_ E.conv) ps ps′
  pars-convertible = a2∷ (expanded tm-atom_type) a2[]

  fields-convertible : All2 (_≈_ E.conv) E.fields fields′
  fields-convertible = a2∷ (expanded (tm-atom_lit "payload"))
    (a2∷ (≈-refl E.conv {t = tm-float_type})
      (a2∷ (≈-refl E.conv {t = tm-float_lit}) a2[]))

  changed-prefix : Spine ⟨⟩ ps′ E.fields E.indices
  changed-prefix = L.spine-locals
    {locals = ps} {locals′ = ps′} pars-convertible E.actual-fields

  computed-results : All2 (_≈_ E.conv)
    (F.instantiateResults ps E.fields (ctor-indices E.computed))
    (F.instantiateResults ps′ fields′ (ctor-indices E.computed))
  computed-results = L.instantiateResults-cong
    {ps = ps} {ps′ = ps′} {fields = E.fields} {fields′ = fields′}
    pars-convertible fields-convertible (ctor-indices E.computed)

  arities : length ps ≡ length ps′ × length E.fields ≡ length fields′
  arities = L.result-arity {ps = ps} {ps′ = ps′}
    {fields = E.fields} {fields′ = fields′} pars-convertible fields-convertible

  -- Neither a closed-body scope assumption nor a prefix-only relation:
  -- the canonical substitution agrees also on surviving caller variables.
  beyond-prefix : _≈_ E.conv
    (F.advance E.fields (F.advance ps F.identity) 6)
    (F.advance fields′ (F.advance ps′ F.identity) 6)
  beyond-prefix = L.result-frame-cong {ps = ps} {ps′ = ps′}
    {fields = E.fields} {fields′ = fields′} pars-convertible fields-convertible 6

  computed-goal-unequal :
    F.instantiateResults ps E.fields (ctor-indices E.computed)
      ≡ F.instantiateResults ps′ fields′ (ctor-indices E.computed) → ⊥
  computed-goal-unequal ()

  applied-motive : _≈_ E.conv
    (Native.apps E.motive-term E.fields)
    (Native.apps (wrap E.motive-term) fields′)
  applied-motive = L.apps-cong {f = E.motive-term} {f′ = wrap E.motive-term}
    {xs = E.fields} {ys = fields′} (expanded E.motive-term) fields-convertible

  computed-branch-goal : _≈_ E.conv
    (Native.branchGoal "NativeComputed" ps E.computed E.motive-term)
    (Native.branchGoal "NativeComputed" ps E.computed (wrap E.motive-term))
  computed-branch-goal =
    L.branchGoal-cong "NativeComputed" ps E.computed
      {m = E.motive-term} {m′ = wrap E.motive-term} (expanded E.motive-term)

  changed-branches : Branches ⟨⟩ E.family ps (wrap E.motive-term) E.branches
  changed-branches = L.branches-motive
    {m = E.motive-term} {m′ = wrap E.motive-term}
    (expanded E.motive-term) (E.branches-typed wf[])
