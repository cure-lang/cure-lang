------------------------------------------------------------------------
-- Invoke actual native whole-source iota preservation at fixed goals.
-- Computed/nonconstant motives and non-head branch selection are real.
-- These do not invoke the old closed-entry soundness theorem.
------------------------------------------------------------------------
module Proof.DependentIotaExamples where

open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Signature using (just-inj)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.TypeHeads
open import Core.Typing using (Ctx; ⟨⟩; Conversion)
open import Core.Reduction
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentTypingControls as Controls
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentIota as Iota
open import Proof.Progress using (FinalTerms; ft[]; ft∷; f-var; f-atom_type; f-atom_lit)

module P = Iota.Preservation E.env E.sig E.conv
module V = P.Valid E.valid
open E.T

ordinary : ∀ {n} {Γ : Ctx n} → WellFormed Γ
  → V.SourceCase Γ "NativeMk" (tm-atom_type ∷ []) E.fields E.motive-term E.branches
ordinary wf = record
  { family = E.family ; ctor = E.mk ; found = refl ; caller = wf
  ; parameters = E.actual-parameters ; arguments = E.actual-fields
  ; result-indices = E.actual-fields ; level = l0
  ; motive-valid = E.motive-valid ; branches = E.branches-typed wf ; coverage = E.coverage }

ordinary-preserved :
  (⟨⟩ ⊢ E.program ⇐ tm-float_type)
  × _⇝_ E.sig E.program tm-float_lit
  × P.T.Check ⟨⟩ tm-float_lit tm-float_type
ordinary-preserved = V.preserve-at (ordinary wf[])
  (tt , tt , tt , tt) Frames.fields-final (tt , tt , tt) refl
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)

computed-x : Term
computed-x = tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) (tm-atom_lit "payload")
computed : V.SourceCase ⟨⟩ "NativeComputed" (tm-atom_type ∷ []) E.fields E.motive-term E.branches
computed = record
  { family = E.family ; ctor = E.computed ; found = refl ; caller = wf[]
  ; parameters = E.actual-parameters ; arguments = E.actual-fields
  ; result-indices = sp∷
      (E.check (⇒-app (⇒-lam ⇒-atom_type (E.check (⇒-var Fin.zero))) ⇒-atom_lit))
      (sp∷ (E.check ⇒-float_type) (sp∷ (E.check ⇒-float_lit) sp[]))
  ; level = l0 ; motive-valid = E.motive-valid
  ; branches = E.branches-typed wf[] ; coverage = E.coverage }
computed-program : Term
computed-program = tm-case (tm-ctor "NativeComputed" E.fields) E.motive-term E.branches
computed-preserved :
  (⟨⟩ ⊢ computed-program ⇐ tm-float_type)
  × _⇝_ E.sig computed-program tm-float_lit
  × P.T.Check ⟨⟩ tm-float_lit tm-float_type
computed-preserved = V.preserve-at computed
  (tt , tt , tt , tt) Frames.fields-final (tt , tt , tt) refl
  (E.motive-reduces computed-x tm-float_type tm-float_lit (tm-ctor "NativeComputed" E.fields))

-- Open ambient callers are checked before the constructor case is formed.
open-source : V.SourceCase E.caller "NativeMk" (tm-atom_type ∷ [])
  E.open-fields E.motive-term E.branches
open-source = record
  { family = E.family ; ctor = E.mk ; found = refl ; caller = E.caller-wf
  ; parameters = E.actual-parameters ; arguments = E.open-spine
  ; result-indices = E.open-spine ; level = l0
  ; motive-valid = E.motive-valid ; branches = E.branches-typed E.caller-wf ; coverage = E.coverage }
open-finals : FinalTerms E.open-fields
open-finals = ft∷ f-var (ft∷ Proof.Progress.f-float_type (ft∷ Proof.Progress.f-float_lit ft[]))
open-preserved :
  (E.caller ⊢ tm-case E.open-value E.motive-term E.branches ⇐ tm-float_type)
  × _⇝_ E.sig (tm-case E.open-value E.motive-term E.branches) tm-float_lit
  × P.T.Check E.caller tm-float_lit tm-float_type
open-preserved = V.preserve-at open-source
  (tt , tt , tt , tt) open-finals (tt , tt , tt) refl
  (E.motive-reduces (tm-var 0) tm-float_type tm-float_lit E.open-value)

-- The SAME motive produces Atom rather than Float when the B field
-- changes. A constant-motive shortcut cannot satisfy these witnesses.
atom-fields : List Term
atom-fields = tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-atom_lit "answer" ∷ []
atom-spine : Spine ⟨⟩ (tm-atom_type ∷ []) atom-fields E.indices
atom-spine = sp∷ (E.check ⇒-atom_lit)
  (sp∷ (E.check ⇒-atom_type) (sp∷ (E.check ⇒-atom_lit) sp[]))
atom-source : V.SourceCase ⟨⟩ "NativeMk" (tm-atom_type ∷ []) atom-fields E.motive-term E.branches
atom-source = record
  { family = E.family ; ctor = E.mk ; found = refl ; caller = wf[]
  ; parameters = E.actual-parameters ; arguments = atom-spine ; result-indices = atom-spine
  ; level = l0 ; motive-valid = E.motive-valid
  ; branches = E.branches-typed wf[] ; coverage = E.coverage }
atom-program : Term
atom-program = tm-case (tm-ctor "NativeMk" atom-fields) E.motive-term E.branches
atom-preserved :
  (⟨⟩ ⊢ atom-program ⇐ tm-atom_type)
  × _⇝_ E.sig atom-program (tm-atom_lit "answer")
  × P.T.Check ⟨⟩ (tm-atom_lit "answer") tm-atom_type
atom-preserved = V.preserve-at atom-source (tt , tt , tt , tt)
  (ft∷ f-atom_lit (ft∷ f-atom_type (ft∷ f-atom_lit ft[]))) (tt , tt , tt) refl
  (E.motive-reduces (tm-atom_lit "payload") tm-atom_type (tm-atom_lit "answer")
    (tm-ctor "NativeMk" atom-fields))

-- Fixed-goal preservation cannot quietly exchange these distinct types.
float-is-not-atom : Conversion._≈_ E.conv tm-float_type tm-atom_type → ⊥
float-is-not-atom equal with Conversion.≈-heads E.conv
  {t = tm-float_type} {u = tm-atom_type} ty-float ty-atom equal
... | ()
wrong-fixed-goal : Conversion._≈_ E.conv
  (Iota.case-goal "NativeMk" (tm-atom_type ∷ []) E.fields E.mk E.motive-term) tm-atom_type → ⊥
wrong-fixed-goal equal = float-is-not-atom
  (Conversion.≈-trans E.conv {t = tm-float_type}
    {u = Iota.case-goal "NativeMk" (tm-atom_type ∷ []) E.fields E.mk E.motive-term}
    {v = tm-atom_type}
    (Conversion.≈-sym E.conv
      {t = Iota.case-goal "NativeMk" (tm-atom_type ∷ []) E.fields E.mk E.motive-term}
      {u = tm-float_type}
      (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)) equal)

missing-coverage-rejected : V.SourceCase ⟨⟩ "NativeMk" (tm-atom_type ∷ [])
  E.fields E.motive-term [] → ⊥
missing-coverage-rejected source with just-inj (V.SourceCase.found source)
... | refl = Controls.missing-coverage (V.SourceCase.coverage source)
wrong-arity-rejected : V.SourceCase ⟨⟩ "NativeMk" (tm-atom_type ∷ [])
  E.fields E.motive-term (("NativeMk" , 4 , tm-var 0) ∷ []) → ⊥
wrong-arity-rejected source with just-inj (V.SourceCase.found source)
... | refl = Controls.wrong-arity-coverage (V.SourceCase.coverage source)
foreign-owner-rejected : ∀ {ar b rest}
  → V.SourceCase ⟨⟩ "NativeMk" (tm-atom_type ∷ []) E.fields E.motive-term
      (("NativeWrap" , ar , b) ∷ rest) → ⊥
foreign-owner-rejected source with just-inj (V.SourceCase.found source)
... | refl = Controls.wrong-owner (V.SourceCase.branches source)
