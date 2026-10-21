------------------------------------------------------------------------
-- Ordinary native iota at ONE fixed goal through arbitrary scrutinee
-- conversions. The SELECTED body contains a complete native nested case.
-- All preservation targets invoke the checked general iota theorem.
------------------------------------------------------------------------
module Proof.DependentGeneralIotaExamples where

open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion; a2[]; a2∷)
open import Core.Reduction
  using (_⇝_; _⇝*_; ⇝*-step; ⇝*-refl; ζ; ξ-pi-dom; ξ-pi-cod; ξ-data-params-at)
open import Core.DependentTyping using (motiveType; Opened; op[]; op∷)
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentIotaBranchExamples as Nested
import Proof.DependentConstructorInversionExamples as Chains
import Proof.DependentDataConversion as Data
import Proof.DependentGeneralIota as General
open E.T

module D = Data.Model E.sig (λ ())
module P = General.Preservation E.env E.sig E.conv E.valid D.data-components

computed-source : P.SourceCase ⟨⟩ "NativeComputed" E.fields E.motive-term
  (Nested.branches (tm-var 0) Nested.nested)
computed-source = record
  { family-name = "NativeD" ; family = E.family
  ; parameters = tm-atom_type ∷ [] ; indices = E.fields
  ; found-family = refl ; caller = wf[]
  ; scrutinee = Chains.computed-chain
  ; parameters-checked = E.actual-parameters ; indices-checked = E.actual-fields
  ; level = Core.Universe.l0 ; motive-valid = E.motive-valid
  ; branches = Nested.mixed-branches
  ; coverage = Nested.coverage (tm-var 0) Nested.nested }

computed-case : Term
computed-case = tm-case (tm-ctor "NativeComputed" E.fields) E.motive-term
  (Nested.branches (tm-var 0) Nested.nested)

computed-selected-nested :
  (⟨⟩ ⊢ computed-case ⇐ tm-float_type)
  × _⇝_ E.sig computed-case E.program
  × (⟨⟩ ⊢ E.program ⇐ tm-float_type)
computed-selected-nested = P.preserve-at computed-source Frames.fields-final refl
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit
    (tm-ctor "NativeComputed" E.fields))

computed-original-indices-distinct : Chains.computed-goal ≡ E.goal → ⊥
computed-original-indices-distinct = Chains.computed-syntax-unequal

ordinary-inference-chain : ⟨⟩ ⊢ E.value ⇒ E.goal
ordinary-inference-chain = ⇒-conv {T = Chains.wrap E.goal} {T′ = E.goal}
  (⇒-conv {T = E.goal} {T′ = Chains.wrap E.goal}
    E.value-typed (Chains.unwrap-converts E.goal))
  (Chains.wrap-converts E.goal)

ordinary-source : P.SourceCase ⟨⟩ "NativeMk" E.fields E.motive-term E.branches
ordinary-source = record
  { family-name = "NativeD" ; family = E.family
  ; parameters = tm-atom_type ∷ [] ; indices = E.fields
  ; found-family = refl ; caller = wf[]
  ; scrutinee = ordinary-inference-chain
  ; parameters-checked = E.actual-parameters ; indices-checked = E.actual-fields
  ; level = Core.Universe.l0 ; motive-valid = E.motive-valid
  ; branches = E.branches-typed wf[] ; coverage = E.coverage }

ordinary-converted-preserved :
  (⟨⟩ ⊢ E.program ⇐ tm-float_type)
  × _⇝_ E.sig E.program tm-float_lit
  × (⟨⟩ ⊢ tm-float_lit ⇐ tm-float_type)
ordinary-converted-preserved = P.preserve-at ordinary-source Frames.fields-final refl
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)

-- The constructor's declarative hidden witness is still Atom. The case
-- uses this different, kind-checked term as its parameter witness.
wrapped-atom : Term
wrapped-atom = tm-let unrestricted (tm-type l0) tm-atom_type (tm-var 0)

wrapped-atom-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ wrapped-atom ⇒ tm-type l0
wrapped-atom-kind = ⇒-let (⇒-type refl) (E.check ⇒-atom_type) (⇒-var Fin.zero)

wrapped-atom-converts : Conversion._≈_ E.conv wrapped-atom tm-atom_type
wrapped-atom-converts = E.R.reduce-converts {t = wrapped-atom} {u = tm-atom_type} ζ

atom-to-wrapped : Conversion._≈_ E.conv tm-atom_type wrapped-atom
atom-to-wrapped = Conversion.≈-sym E.conv
  {t = wrapped-atom} {u = tm-atom_type} wrapped-atom-converts

wrapped-not-syntactically-atom : wrapped-atom ≡ tm-atom_type → ⊥
wrapped-not-syntactically-atom ()

wrapped-parameters : ∀ {n} {Γ : Ctx n}
  → Spine Γ [] (wrapped-atom ∷ []) E.parameters
wrapped-parameters = sp∷ (E.check wrapped-atom-kind) sp[]

wrapped-actual-indices : Spine ⟨⟩ (wrapped-atom ∷ []) E.fields E.indices
wrapped-actual-indices = sp∷ (⇐-infer ⇒-atom_lit atom-to-wrapped)
  (sp∷ (E.check ⇒-float_type) (sp∷ (E.check ⇒-float_lit) sp[]))

FreshWrapped : ∀ {n} → Ctx n → Ctx (3 Data.Nat.+ n)
FreshWrapped Γ = extend (extend (extend Γ wrapped-atom) (tm-type l0)) (tm-var 0)

wrapped-opening : Opened ⟨⟩ (F.advance (wrapped-atom ∷ []) F.identity)
  E.indices (FreshWrapped ⟨⟩)
wrapped-opening = op∷ (op∷ (op∷ op[]))

wrapped-fresh-wf : WellFormed (FreshWrapped ⟨⟩)
wrapped-fresh-wf = wf∷
  (wf∷ (wf∷ wf[] (P.G.Sc.infer-scoped (wrapped-atom-kind {Γ = ⟨⟩})) wrapped-atom-kind)
    sc-type (⇒-type refl))
  (sc-var (s≤s z≤n)) (⇒-var Fin.zero)

wrapped-fresh-kind : ∀ {n} {Γ : Ctx n} → FreshWrapped Γ ⊢
  tm-data "NativeD" (wrapped-atom ∷ []) Nested.fresh-fields ⇒ tm-type l1
wrapped-fresh-kind = ⇒-data refl wrapped-parameters
  (sp∷ (E.check (⇒-var (Fin.suc (Fin.suc Fin.zero))))
    (sp∷ (E.check (⇒-var (Fin.suc Fin.zero))) (sp∷ (E.check (⇒-var Fin.zero)) sp[])))

wrapped-motive-kind : ⟨⟩ ⊢ motiveType E.family (wrapped-atom ∷ []) l0 ⇒ tm-type l1
wrapped-motive-kind = ⇒-pi wrapped-atom-kind (⇒-pi (⇒-type refl)
  (⇒-pi (⇒-var Fin.zero) (⇒-pi wrapped-fresh-kind (⇒-type refl))))

-- This is an explicit model reduction, NOT a motiveType conversion
-- oracle: reduce the first Pi domain, then its scrutinee data parameter.
wrapped-motive-type-path : _⇝*_ E.sig
  (motiveType E.family (wrapped-atom ∷ []) l0)
  (motiveType E.family (tm-atom_type ∷ []) l0)
wrapped-motive-type-path = ⇝*-step (ξ-pi-dom ζ)
  (⇝*-step (ξ-pi-cod (ξ-pi-cod (ξ-pi-cod (ξ-pi-dom (ξ-data-params-at Fin.zero ζ))))) ⇝*-refl)

wrapped-motive-type-equal : Conversion._≈_ E.conv
  (motiveType E.family (wrapped-atom ∷ []) l0)
  (motiveType E.family (tm-atom_type ∷ []) l0)
wrapped-motive-type-equal = E.path-converts wrapped-motive-type-path

wrapped-motive : Motive ⟨⟩ E.family (wrapped-atom ∷ []) E.motive-term l0
wrapped-motive = motive E.motive-scoped wrapped-motive-kind
  (⇒-conv E.motive-typed
    (Conversion.≈-sym E.conv
      {t = motiveType E.family (wrapped-atom ∷ []) l0}
      {u = motiveType E.family (tm-atom_type ∷ []) l0}
      wrapped-motive-type-equal))

wrapped-context-agrees : P.V.Contexts (E.Fresh ⟨⟩) (FreshWrapped ⟨⟩)
wrapped-context-agrees Fin.zero = Conversion.≈-refl E.conv {t = tm-var 1}
wrapped-context-agrees (Fin.suc Fin.zero) = Conversion.≈-refl E.conv {t = tm-type l0}
wrapped-context-agrees (Fin.suc (Fin.suc Fin.zero)) = atom-to-wrapped
wrapped-context-agrees (Fin.suc (Fin.suc (Fin.suc ())))

wrapped-nested-typed : FreshWrapped ⟨⟩ ⊢ Nested.nested ⇒ tm-var 1
wrapped-nested-typed =
  P.V.context⇒ wrapped-context-agrees wrapped-fresh-wf Nested.nested-typed

wrapped-branches : Branches ⟨⟩ E.family (wrapped-atom ∷ []) E.motive-term
  (Nested.branches (tm-var 0) Nested.nested)
wrapped-branches = br∷ refl refl wrapped-opening wrapped-fresh-wf
  (⇐-infer (⇒-var Fin.zero)
    (E.motive-symmetric (tm-var 2) (tm-var 1) (tm-var 0)
      (tm-ctor "NativeMk" Nested.fresh-fields)))
  (br∷ refl refl wrapped-opening wrapped-fresh-wf
    (⇐-infer wrapped-nested-typed
      (E.motive-symmetric
        (F.specializeParameters 3 (wrapped-atom ∷ []) E.computed-index)
        (tm-var 1) (tm-var 0) (tm-ctor "NativeComputed" Nested.fresh-fields))) br[])

wrapped-goal : Term
wrapped-goal = tm-data "NativeD" (wrapped-atom ∷ []) E.fields

goal-to-wrapped : Conversion._≈_ E.conv E.goal wrapped-goal
goal-to-wrapped = Conversion.≈-data E.conv
  {n = "NativeD"} {ps = tm-atom_type ∷ []} {ps′ = wrapped-atom ∷ []}
  {is = E.fields} {is′ = E.fields}
  (a2∷ atom-to-wrapped a2[])
  (a2∷ (Conversion.≈-refl E.conv {t = tm-atom_lit "payload"})
    (a2∷ (Conversion.≈-refl E.conv {t = tm-float_type})
      (a2∷ (Conversion.≈-refl E.conv {t = tm-float_lit}) a2[])))

wrapped-scrutinee : ⟨⟩ ⊢ tm-ctor "NativeComputed" E.fields ⇒ wrapped-goal
wrapped-scrutinee = ⇒-conv Chains.computed-chain goal-to-wrapped

wrapped-source : P.SourceCase ⟨⟩ "NativeComputed" E.fields E.motive-term
  (Nested.branches (tm-var 0) Nested.nested)
wrapped-source = record
  { family-name = "NativeD" ; family = E.family
  ; parameters = wrapped-atom ∷ [] ; indices = E.fields
  ; found-family = refl ; caller = wf[] ; scrutinee = wrapped-scrutinee
  ; parameters-checked = wrapped-parameters ; indices-checked = wrapped-actual-indices
  ; level = l0 ; motive-valid = wrapped-motive
  ; branches = wrapped-branches ; coverage = Nested.coverage (tm-var 0) Nested.nested }

wrapped-parameter-selected-nested :
  (⟨⟩ ⊢ computed-case ⇐ tm-float_type)
  × _⇝_ E.sig computed-case E.program
  × (⟨⟩ ⊢ E.program ⇐ tm-float_type)
wrapped-parameter-selected-nested = P.preserve-at wrapped-source Frames.fields-final refl
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit
    (tm-ctor "NativeComputed" E.fields))
