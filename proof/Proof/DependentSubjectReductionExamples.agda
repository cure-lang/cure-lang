------------------------------------------------------------------------
-- Examples call recursive native preservation on source derivations.
-- No independently typed endpoints are passed to the theorem.
------------------------------------------------------------------------
module Proof.DependentSubjectReductionExamples where

import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l0≤l1)
open import Core.Signature using (just-inj)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Reduction
import Core.LocalFrame as F
open import Proof.Progress using
  (Final; FinalTerms; FinalBranches; BodiesFinal;
   f-var; f-type; f-lam; f-let; f-case; f-data; f-ctor; f-atom_type;
   f-atom_lit; f-float_type; f-float_lit; f-global; ft[]; ft∷; fb[]; fb∷)
import Proof.DependentTypingExamples as E
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentIotaBranchExamples as Nested
import Proof.DependentGeneralIotaExamples as General
import Proof.DependentCongruenceExamples as Congruence
import Proof.DependentRootExamples as Root
import Proof.DependentDataConversion as Data
import Proof.DependentLiteralPreservation as Literal
import Proof.DependentSubjectReduction as Subject

bodies-final : BodiesFinal E.sig
bodies-final ()
shapes : Literal.BuiltinShapes E.env
shapes = record { nat-shape = λ (); bounded-shape = λ () }
module D = Data.Model E.sig (λ ())
module P = Subject.Preserve E.env E.sig E.conv E.valid D.data-components
  (λ {t} {u} → E.R.reduce-converts {t} {u})
  (λ {f} {body′} → bodies-final {f} {body′}) shapes
open E.T

-- Complete finality evidence, including the dependent motive's data
-- domain and every branch body, rather than just the selected branch.
motive-final : Final E.motive-term
motive-final = f-lam f-atom_type (f-lam f-type (f-lam f-var
  (f-lam (f-data (ft∷ f-atom_type ft[])
    (ft∷ f-var (ft∷ f-var (ft∷ f-var ft[])))) f-var)))
branches-final : FinalBranches E.branches
branches-final = fb∷ f-var (fb∷ f-var fb[])
program-final : Final E.program
program-final = f-case (f-ctor Frames.fields-final) motive-final branches-final
nested-final : Final Nested.nested
nested-final = f-case
  (f-ctor (ft∷ f-var (ft∷ f-var (ft∷ f-var ft[]))))
  motive-final branches-final
computed-final : Final General.computed-case
computed-final = f-case (f-ctor Frames.fields-final) motive-final
  (fb∷ f-var (fb∷ nested-final fb[]))

-- This source uses the let-wrapped parameter, converted constructor
-- result and the genuinely nested selected body from General's fixture.
-- Construct its source derivation, not the old iota theorem's endpoint.
wrapped-nested-source : ⟨⟩ ⊢ General.computed-case ⇒ tm-float_type
wrapped-nested-source = ⇒-conv
  (⇒-case wf[] refl General.wrapped-scrutinee General.wrapped-parameters
    General.wrapped-actual-indices General.wrapped-motive
    General.wrapped-branches (Nested.coverage (tm-var 0) Nested.nested))
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit
    (tm-ctor "NativeComputed" E.fields))
selected-nested-step : _⇝_ E.sig General.computed-case E.program
selected-nested-step = ι refl refl
selected-nested-recursive : ⟨⟩ ⊢ E.program ⇐ tm-float_type
selected-nested-recursive =
  P.preservation⇒ wf[] wrapped-nested-source computed-final selected-nested-step
selected-nested-infers : ⟨⟩ ⊢ E.program ⇒ tm-float_type
selected-nested-infers =
  P.preservation-infers wf[] wrapped-nested-source computed-final selected-nested-step
nested-two-step : _⇝*_ E.sig General.computed-case tm-float_lit
nested-two-step = ⇝*-step selected-nested-step (⇝*-step (ι refl refl) ⇝*-refl)
nested-two-step-recursive : ⟨⟩ ⊢ tm-float_lit ⇐ tm-float_type
nested-two-step-recursive =
  P.preservation-star⇐ wf[] (E.check wrapped-nested-source) computed-final nested-two-step

lambda-source : ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type E.program
  ⇒ tm-pi unrestricted tm-atom_type tm-float_type
lambda-source = ⇒-lam ⇒-atom_type (E.check Congruence.nested-case-source)
lambda-body-recursive :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type tm-float_lit
    ⇐ tm-pi unrestricted tm-atom_type tm-float_type
lambda-body-recursive = P.preservation⇒ wf[] lambda-source
  (f-lam f-atom_type program-final) (ξ-lam-body (ι refl refl))
checked-lambda-body-recursive :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type tm-float_lit
    ⇐ tm-pi unrestricted tm-atom_type tm-float_type
checked-lambda-body-recursive = P.preservation⇐ wf[]
  (⇐-lam ⇒-atom_type (E.check Congruence.nested-case-source))
  (f-lam f-atom_type program-final) (ξ-lam-body (ι refl refl))
atom-computation-kind : ∀ {n} {Γ : Ctx n}
  → Γ ⊢ Congruence.atom-computation ⇒ tm-type l0
atom-computation-kind = ⇒-let ⇒-atom_type (E.check ⇒-atom_lit) ⇒-atom_type
atom-computation-final : Final Congruence.atom-computation
atom-computation-final = f-let f-atom_type f-atom_lit f-atom_type
lambda-domain-source :
  ⟨⟩ ⊢ tm-lam unrestricted Congruence.atom-computation (tm-var 0)
    ⇒ tm-pi unrestricted Congruence.atom-computation Congruence.atom-computation
lambda-domain-source = ⇒-lam atom-computation-kind (E.check (⇒-var Fin.zero))
lambda-domain-recursive :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-var 0)
    ⇐ tm-pi unrestricted Congruence.atom-computation Congruence.atom-computation
lambda-domain-recursive = P.preservation⇒ wf[] lambda-domain-source
  (f-lam atom-computation-final f-var) (ξ-lam-dom ζ)

float-computation-final : Final Congruence.float-computation
float-computation-final = f-let f-atom_type f-atom_lit f-float_type
source-fields-final : FinalTerms Congruence.source-fields
source-fields-final =
  ft∷ f-atom_lit (ft∷ float-computation-final (ft∷ f-float_lit ft[]))
non-head-field-source :
  ⟨⟩ ⊢ tm-ctor "NativeMk" Congruence.source-fields ⇒ Congruence.source-goal
non-head-field-source = ⇒-ctor refl E.actual-parameters Congruence.source-spine
non-head-field-recursive : ⟨⟩ ⊢ E.value ⇐ Congruence.source-goal
non-head-field-recursive = P.preservation⇒ wf[] non-head-field-source
  (f-ctor source-fields-final) (ξ-ctor-at (Fin.suc Fin.zero) ζ)
non-head-index-recursive : ⟨⟩ ⊢ E.goal ⇐ tm-type l1
non-head-index-recursive = P.preservation⇒ wf[]
  (⇒-data refl E.actual-parameters Congruence.source-spine)
  (f-data (ft∷ f-atom_type ft[]) source-fields-final)
  (ξ-data-indices-at (Fin.suc Fin.zero) ζ)

-- Two real body reductions under fresh branch fields. Their intermediate
-- checking evidence is generated recursively by preservation-star⇐.
double-let : Term
double-let = tm-let unrestricted tm-atom_type (tm-atom_lit "ignored")
  (tm-let unrestricted tm-atom_type (tm-atom_lit "ignored") (tm-var 2))
double-let-final : Final double-let
double-let-final = f-let f-atom_type f-atom_lit (f-let f-atom_type f-atom_lit f-var)
double-let-typed : E.Fresh ⟨⟩ ⊢ double-let ⇒ tm-var 1
double-let-typed = ⇒-let ⇒-atom_type (E.check ⇒-atom_lit)
  (⇒-let ⇒-atom_type (E.check ⇒-atom_lit)
    (⇒-var (Fin.suc (Fin.suc Fin.zero))))
branch-source : List Branch
branch-source = Nested.branches double-let (tm-var 0)
branch-source-typed : Branches ⟨⟩ E.family (tm-atom_type ∷ []) E.motive-term branch-source
branch-source-typed = br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
  (⇐-infer double-let-typed
    (E.motive-symmetric (tm-var 2) (tm-var 1) (tm-var 0)
      (tm-ctor "NativeMk" Nested.fresh-fields)))
  (br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
    (⇐-infer (⇒-var Fin.zero)
      (E.motive-symmetric
        (F.specializeParameters 3 (tm-atom_type ∷ []) E.computed-index)
        (tm-var 1) (tm-var 0) (tm-ctor "NativeComputed" Nested.fresh-fields))) br[])
branch-source-final : FinalBranches branch-source
branch-source-final = fb∷ double-let-final (fb∷ f-var fb[])
branch-body-path : _⇝*_ E.sig double-let (tm-var 0)
branch-body-path = ⇝*-step ζ (⇝*-step ζ ⇝*-refl)
branches-path : _⇝*ᵇ_ E.sig branch-source E.branches
branches-path = ⇝ᵇ-cons branch-body-path (⇝ᵇ-cons ⇝*-refl ⇝ᵇ-nil)
branches-recursive : Branches ⟨⟩ E.family (tm-atom_type ∷ []) E.motive-term E.branches
branches-recursive = P.preservation-branches branch-source-typed branch-source-final branches-path
branch-program : Term
branch-program = tm-case E.value E.motive-term branch-source
branch-program-typed : ⟨⟩ ⊢ branch-program ⇒ tm-float_type
branch-program-typed = ⇒-conv
  (⇒-case wf[] refl E.value-typed E.actual-parameters E.actual-fields E.motive-valid
    branch-source-typed (Nested.coverage double-let (tm-var 0)))
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)
branch-program-final : Final branch-program
branch-program-final = f-case (f-ctor Frames.fields-final) motive-final branch-source-final
branch-congruence-recursive : ⟨⟩ ⊢ E.program ⇐ tm-float_type
branch-congruence-recursive = P.preservation⇒ wf[] branch-program-typed
  branch-program-final (ξ-case-brs branches-path)
branch-then-iota-recursive : ⟨⟩ ⊢ tm-float_lit ⇐ tm-float_type
branch-then-iota-recursive = P.preservation-star⇐ wf[] (E.check branch-program-typed)
  branch-program-final (⇝*-step (ξ-case-brs branches-path) (⇝*-step (ι refl refl) ⇝*-refl))

-- Conversion wrappers followed by actual universe cumulativity, around
-- a reducible term; the theorem must recurse through both wrappers.
wrapped-sort : Term
wrapped-sort = tm-let unrestricted tm-atom_type (tm-atom_lit "ignored") (tm-type l0)
sort-wrap : Conversion._≈_ E.conv (tm-type l0) wrapped-sort
sort-wrap = Conversion.≈-sym E.conv {t = wrapped-sort} {u = tm-type l0}
  (E.R.reduce-converts {t = wrapped-sort} {u = tm-type l0} ζ)
cumulative-source : ⟨⟩ ⊢ Congruence.float-computation ⇒ tm-type l1
cumulative-source = ⇒-cumul
  (⇒-conv {T = wrapped-sort} {T′ = tm-type l0}
    (⇒-conv {T = tm-type l0} {T′ = wrapped-sort}
      Congruence.float-computation-kind sort-wrap)
    (E.R.reduce-converts {t = wrapped-sort} {u = tm-type l0} ζ)) l0≤l1
converted-cumulative-recursive : ⟨⟩ ⊢ tm-float_type ⇐ tm-type l1
converted-cumulative-recursive = P.preservation⇒ wf[] cumulative-source float-computation-final ζ
checked-cumulative-recursive : ⟨⟩ ⊢ tm-float_type ⇐ tm-type l1
checked-cumulative-recursive = P.preservation⇐ wf[]
  (⇐-conv {T = tm-type l1} {T′ = tm-type l1}
    (⇐-cumul {i = l0} {j = l1} Congruence.float-computation-kind l0≤l1)
    (Conversion.≈-refl E.conv {t = tm-type l1}))
  float-computation-final ζ

module Globals where
  module G = Root.Globals
  module GD = Data.Model G.sig (λ {name} {b} → G.body-closed {name} {b})
  value-final : Final G.value
  value-final = f-ctor (ft∷ f-atom_lit ft[])
  global-bodies-final : BodiesFinal G.sig
  global-bodies-final {f} found with f ≟ "native-root"
  ... | yes equal with just-inj found
  ... | refl = value-final
  global-bodies-final {f} () | no different
  global-shapes : Literal.BuiltinShapes G.env
  global-shapes = record { nat-shape = λ (); bounded-shape = λ () }
  module GP = Subject.Preserve G.env G.sig G.conv G.Witnesses.valid GD.data-components
    (λ {t} {u} → G.R.reduce-converts {t} {u}) global-bodies-final global-shapes
  source : G.N._⊢_⇒_ ⟨⟩ (tm-global "native-root") G.goal
  source = G.N.⇒-conv (G.N.⇒-global refl)
    (G.R.reduce-converts {t = G.declared-type} {u = G.goal} ζ)
  delta-recursive : G.N._⊢_⇐_ ⟨⟩ G.value G.goal
  delta-recursive = GP.preservation⇒ G.N.wf[] source f-global (δ refl)
  delta-declared-recursive : G.N._⊢_⇒_ ⟨⟩ G.value G.declared-type
  delta-declared-recursive =
    GP.preservation-infers G.N.wf[]
      (G.N.⇒-global {name = "native-root"} {T = G.declared-type} refl)
      f-global (δ {f = "native-root"} refl)
