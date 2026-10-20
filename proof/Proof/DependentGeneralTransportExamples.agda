------------------------------------------------------------------------
-- General native transport regressions: whole-case images, capture under
-- binders, and nested cases in source branches. Targets invoke the actual
-- general theorem, never a case-free support certificate.
------------------------------------------------------------------------
module Proof.DependentGeneralTransportExamples where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.TypeHeads using (ty-atom; ty-float)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Reduction using (substArgs; _⇝*_; ⇝*-step; ⇝*-refl; ξ-app₁; β; ζ)
open import Core.Universe using (l0; l1; l2)
open import Core.Signature using (Telescope)
open import Core.DependentTyping using (Opened; op[]; op∷; apps; motiveType)
import Core.LocalFrame as F
import Proof.Substitution as S
import Proof.DependentContextSuffix as Suffix
import Proof.DependentTypingExamples as E
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentIotaBranchExamples as Nested
import Proof.DependentTypingInversion as Inversion
import Proof.DependentGeneralTransport as General

module G = General.General E.env E.sig E.conv
module V = G.Valid E.valid
module C = G.C
module I = Inversion.Laws E.env E.sig E.conv
open E.T

-- Unlike the fragment theorem, a complete CASE can be a substitution
-- image. Passing underneath the lambda weakens that image natively.
case-image : C.Coherent (extend ⟨⟩ tm-float_type) ⟨⟩ (topSub E.program)
case-image = V.top-coherent E.program-typed

capture-source : extend ⟨⟩ tm-float_type ⊢
  tm-lam unrestricted tm-atom_type (tm-var 1)
  ⇒ tm-pi unrestricted tm-atom_type tm-float_type
capture-source = ⇒-lam ⇒-atom_type (E.check (⇒-var (Fin.suc Fin.zero)))

case-image-under-lambda : ⟨⟩ ⊢
  tm-lam unrestricted tm-atom_type E.program
  ⇒ tm-pi unrestricted tm-atom_type tm-float_type
case-image-under-lambda = V.subst⇒ case-image wf[] capture-source

case-image-under-checking-lambda : ⟨⟩ ⊢
  tm-lam unrestricted tm-atom_type E.program
  ⇐ tm-pi unrestricted tm-atom_type tm-float_type
case-image-under-checking-lambda = V.subst⇐ case-image wf[] (E.check capture-source)

open-program : Term
open-program = tm-case E.open-value E.motive-term E.branches

open-case-image : C.Coherent (extend E.caller tm-float_type) E.caller (topSub open-program)
open-case-image = V.top-coherent E.open-typed

open-capture-source : extend E.caller tm-float_type ⊢
  tm-lam unrestricted tm-atom_type (tm-var 1)
  ⇒ tm-pi unrestricted tm-atom_type tm-float_type
open-capture-source = ⇒-lam ⇒-atom_type (E.check (⇒-var (Fin.suc Fin.zero)))

-- The image's ambient Atom slot must move to 1 under the new binder,
-- not become that lambda's bound slot 0.
shifted-open-program : Term
shifted-open-program = tm-case
  (tm-ctor "NativeMk" (tm-var 1 ∷ tm-float_type ∷ tm-float_lit ∷ []))
  E.motive-term E.branches

open-case-capture-avoiding : E.caller ⊢
  tm-lam unrestricted tm-atom_type shifted-open-program
  ⇒ tm-pi unrestricted tm-atom_type tm-float_type
open-case-capture-avoiding =
  V.subst⇒ open-case-image E.caller-wf open-capture-source

capture-algorithm-exact :
  substS (topSub open-program) (tm-lam unrestricted tm-atom_type (tm-var 1))
    ≡ tm-lam unrestricted tm-atom_type shifted-open-program
capture-algorithm-exact = refl

wrong-capture-rejected :
  substS (topSub open-program) (tm-lam unrestricted tm-atom_type (tm-var 1))
    ≡ tm-lam unrestricted tm-atom_type open-program → ⊥
wrong-capture-rejected ()

-- Formerly unsupported SELECTED nested branch body now contracts with
-- the native general theorem. No selected-support premise remains.
nested-branch-contracted : ⟨⟩ ⊢ E.program ⇐ tm-float_type
nested-branch-contracted = V.contract-branch {ps = tm-atom_type ∷ []}
  wf[] E.fresh-opening E.actual-fields Frames.fields-final
  (E.check Nested.nested-typed)

-- A source whose second branch contains a whole case tests traversal of
-- ALL branch derivations, not merely the selected first branch.
mixed-source : ⟨⟩ ⊢ Nested.mixed-program ⇒ tm-float_type
mixed-source = ⇒-conv
  (⇒-case wf[] refl E.value-typed E.actual-parameters E.actual-fields
    E.motive-valid Nested.mixed-branches (Nested.coverage (tm-var 0) Nested.nested))
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)

mixed-source-weakened : E.caller ⊢ Nested.mixed-program ⇒ tm-float_type
mixed-source-weakened =
  V.rename⇒ (C.weakening ⟨⟩ tm-atom_type) E.caller-wf mixed-source

mixed-source-reclosed : ⟨⟩ ⊢ Nested.mixed-program ⇒ tm-float_type
mixed-source-reclosed =
  V.subst⇒ (V.top-coherent (⇒-atom_lit {name = "ambient"})) wf[] mixed-source-weakened

arbitrary-nested-weakened : extend (E.Fresh ⟨⟩) tm-atom_type ⊢
  rename wk Nested.nested ⇒ tm-var 2
arbitrary-nested-weakened = V.rename⇒
  (C.weakening (E.Fresh ⟨⟩) tm-atom_type)
  (wf∷ (E.fresh-wf wf[]) sc-atom_type ⇒-atom_type) Nested.nested-typed

mixed-context-transported : ⟨⟩ ⊢ Nested.mixed-program ⇐ tm-float_type
mixed-context-transported = V.context⇐ (λ ())
  wf[] (E.check mixed-source)

-- Checking holes transport, but cannot become coherent inference images.
hole-transported : ⟨⟩ ⊢ tm-hole "pending" ⇐ tm-atom_type
hole-transported = V.subst⇐ (C.identity ⟨⟩) wf[] Frames.hole-checked

hole-image-rejected : C.Coherent (extend ⟨⟩ tm-atom_type)
  ⟨⟩ (topSub (tm-hole "pending")) → ⊥
hole-image-rejected = Frames.hole-not-coherent

-- The general theorem still demands correctly typed images. Abstract
-- rigid-head inversion, not concrete conversion-model reduction, rejects
-- replacing a Float slot by an Atom literal.
wrong-image-rejected : C.Coherent (extend ⟨⟩ tm-float_type)
  ⟨⟩ (topSub (tm-atom_lit "wrong")) → ⊥
wrong-image-rejected coh
  with Conversion.≈-heads E.conv {t = tm-atom_type} {u = tm-float_type}
    ty-atom ty-float (I.atom-inference (coh Fin.zero))
... | ()

wrong-dependent-frame-rejected : C.Coherent E.Φ ⟨⟩
  (F.advance Frames.wrong-fields (F.advance (tm-atom_type ∷ []) F.identity)) → ⊥
wrong-dependent-frame-rejected = Frames.wrong-slot-rejected

-- A native case occurs INSIDE the motive's inference derivation. Its
-- surrounding let reduces, but the transport proof must still traverse
-- the original case premise rather than only inspecting target syntax.
nested-motive : Term
nested-motive = tm-let unrestricted tm-float_type E.program E.motive-term

nested-motive-typed : ⟨⟩ ⊢ nested-motive
  ⇒ motiveType E.family (tm-atom_type ∷ []) l0
nested-motive-typed = ⇒-let ⇒-float_type (E.check E.program-typed) E.motive-typed

nested-motive-equal : ∀ x B y s → Conversion._≈_ E.conv
  (apps nested-motive (x ∷ B ∷ y ∷ s ∷ [])) B
nested-motive-equal x B y s = Conversion.≈-trans E.conv
  {t = apps nested-motive (x ∷ B ∷ y ∷ s ∷ [])}
  {u = apps E.motive-term (x ∷ B ∷ y ∷ s ∷ [])} {v = B}
  (E.R.reduce-converts
    {t = apps nested-motive (x ∷ B ∷ y ∷ s ∷ [])}
    {u = apps E.motive-term (x ∷ B ∷ y ∷ s ∷ [])}
    (ξ-app₁ (ξ-app₁ (ξ-app₁ (ξ-app₁ ζ)))))
  (E.motive-reduces x B y s)

nested-motive-branches : Branches ⟨⟩ E.family (tm-atom_type ∷ []) nested-motive E.branches
nested-motive-branches = br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
  (⇐-infer (⇒-var Fin.zero)
    (Conversion.≈-sym E.conv
      {t = apps nested-motive
        (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ tm-ctor "NativeMk" Nested.fresh-fields ∷ [])}
      {u = tm-var 1}
      (nested-motive-equal (tm-var 2) (tm-var 1) (tm-var 0)
        (tm-ctor "NativeMk" Nested.fresh-fields))))
  (br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
    (⇐-infer (⇒-var Fin.zero)
      (Conversion.≈-sym E.conv
        {t = apps nested-motive
          (F.specializeParameters 3 (tm-atom_type ∷ []) E.computed-index ∷
            tm-var 1 ∷ tm-var 0 ∷ tm-ctor "NativeComputed" Nested.fresh-fields ∷ [])}
        {u = tm-var 1}
        (nested-motive-equal
          (F.specializeParameters 3 (tm-atom_type ∷ []) E.computed-index)
          (tm-var 1) (tm-var 0) (tm-ctor "NativeComputed" Nested.fresh-fields)))) br[])

motive-source : Term
motive-source = tm-case E.value nested-motive E.branches

motive-source-typed : ⟨⟩ ⊢ motive-source ⇒ tm-float_type
motive-source-typed = ⇒-conv
  (⇒-case wf[] refl E.value-typed E.actual-parameters E.actual-fields
    (motive (G.Sc.infer-scoped nested-motive-typed) E.motive-kind nested-motive-typed)
    nested-motive-branches E.coverage)
  (nested-motive-equal (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)

nested-motive-weakened : E.caller ⊢ motive-source ⇒ tm-float_type
nested-motive-weakened =
  V.rename⇒ (C.weakening ⟨⟩ tm-atom_type) E.caller-wf motive-source-typed

nested-motive-substituted : ⟨⟩ ⊢ motive-source ⇐ tm-float_type
nested-motive-substituted = V.subst⇐
  (V.top-coherent (⇒-atom_lit {name = "motive-ambient"}))
  wf[] (E.check nested-motive-weakened)

-- This case RETURNS a type, so its native derivation can be the kind
-- premise of an actual wf∷. The opening tests below force the mutual
-- opening theorem to recurse through that original kind's ⇒-case.
type-motive : Term
type-motive = tm-lam unrestricted tm-atom_type
  (tm-lam unrestricted (tm-type l0) (tm-lam unrestricted (tm-var 0)
    (tm-lam unrestricted E.scrutinee-domain (tm-type l0))))

type-motive-kind : ⟨⟩ ⊢ motiveType E.family (tm-atom_type ∷ []) l1 ⇒ tm-type l2
type-motive-kind = ⇒-pi ⇒-atom_type (⇒-pi (⇒-type refl)
  (⇒-pi (⇒-var Fin.zero) (⇒-pi E.fresh-kind (⇒-type refl))))

type-motive-typed : ⟨⟩ ⊢ type-motive ⇒ motiveType E.family (tm-atom_type ∷ []) l1
type-motive-typed = ⇒-lam ⇒-atom_type (⇐-lam (⇒-type refl)
  (⇐-lam (⇒-var Fin.zero) (⇐-lam E.fresh-kind (E.check (⇒-type refl)))))

type-motive-path : ∀ x B y s → _⇝*_ E.sig
  (apps type-motive (x ∷ B ∷ y ∷ s ∷ [])) (tm-type l0)
type-motive-path x B y s = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))

type-motive-equal : ∀ x B y s → Conversion._≈_ E.conv
  (apps type-motive (x ∷ B ∷ y ∷ s ∷ [])) (tm-type l0)
type-motive-equal x B y s = E.path-converts (type-motive-path x B y s)

type-branches : List Branch
type-branches = Nested.branches tm-float_type tm-float_type

type-branches-typed : Branches ⟨⟩ E.family (tm-atom_type ∷ []) type-motive type-branches
type-branches-typed = br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
  (⇐-infer ⇒-float_type
    (Conversion.≈-sym E.conv
      {t = apps type-motive
        (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ tm-ctor "NativeMk" Nested.fresh-fields ∷ [])}
      {u = tm-type l0}
      (type-motive-equal (tm-var 2) (tm-var 1) (tm-var 0)
        (tm-ctor "NativeMk" Nested.fresh-fields))))
  (br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
    (⇐-infer ⇒-float_type
      (Conversion.≈-sym E.conv
        {t = apps type-motive
          (F.specializeParameters 3 (tm-atom_type ∷ []) E.computed-index ∷
            tm-var 1 ∷ tm-var 0 ∷ tm-ctor "NativeComputed" Nested.fresh-fields ∷ [])}
        {u = tm-type l0}
        (type-motive-equal
          (F.specializeParameters 3 (tm-atom_type ∷ []) E.computed-index)
          (tm-var 1) (tm-var 0) (tm-ctor "NativeComputed" Nested.fresh-fields)))) br[])

type-case : Term
type-case = tm-case E.value type-motive type-branches

type-case-kind : ⟨⟩ ⊢ type-case ⇒ tm-type l0
type-case-kind = ⇒-conv
  (⇒-case wf[] refl E.value-typed E.actual-parameters E.actual-fields
    (motive (G.Sc.infer-scoped type-motive-typed) type-motive-kind type-motive-typed)
    type-branches-typed (Nested.coverage tm-float_type tm-float_type))
  (type-motive-equal (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)

type-case-wf : WellFormed (extend ⟨⟩ type-case)
type-case-wf = wf∷ wf[] (G.Sc.infer-scoped type-case-kind) type-case-kind

type-tele : Telescope
type-tele = ("type-valued-case" , type-case) ∷ []

type-case-opening : Opened ⟨⟩ F.identity type-tele (extend ⟨⟩ type-case)
type-case-opening = op∷ op[]

renamed-case-kind-opening :
  Σ ℕ (λ n → Σ (Ctx n) (λ Ω → WellFormed Ω
    × Opened E.caller (S.renameSub wk F.identity) type-tele Ω
    × C.Renaming (extend ⟨⟩ type-case) Ω (ext wk)))
renamed-case-kind-opening = V.rename-opening type-case-wf
  (Suffix.opened-snoc type-case-opening) refl
  (C.weakening ⟨⟩ tm-atom_type) E.caller-wf

substituted-case-kind-opening :
  Σ ℕ (λ n → Σ (Ctx n) (λ Ω → WellFormed Ω
    × Opened ⟨⟩ (S.substCompose F.identity F.identity) type-tele Ω
    × C.Coherent (extend ⟨⟩ type-case) Ω (extSub F.identity)))
substituted-case-kind-opening = V.subst-opening type-case-wf
  (Suffix.opened-snoc type-case-opening) refl (C.identity ⟨⟩) wf[]
