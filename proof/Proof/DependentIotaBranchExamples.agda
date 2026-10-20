------------------------------------------------------------------------
-- Whole native source cases with capture and with an unused nested case.
-- Fragment support belongs to the SELECTED branch, not every branch.
------------------------------------------------------------------------
module Proof.DependentIotaBranchExamples where

open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Signature
open import Core.Coverage
open import Core.Typing using (Ctx; ⟨⟩; Conversion)
open import Core.Reduction
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentIota as Iota

module P = Iota.Preservation E.env E.sig E.conv
module V = P.Valid E.valid
open E.T

branches : Term → Term → List Branch
branches first second = ("NativeMk" , 3 , first) ∷ ("NativeComputed" , 3 , second) ∷ []

covered-ctor : ∀ first second {name f ct}
  → findCtor name (IndEnv.families E.env) ≡ just (f , ct)
  → fam-name f ≡ "NativeD" → HasBranch name (length (ctor-args ct)) (branches first second)
covered-ctor first second {name} found owner
  with lookup-ctor-members {c = name} {fs = IndEnv.families E.env} found
... | here refl , here refl , refl = first , refl
... | here refl , there (here refl) , refl = second , refl
... | here refl , there (there ()) , equal
covered-ctor first second found () | there (here refl) , member , equal
covered-ctor first second found owner | there (there ()) , member , equal
coverage : ∀ first second → CaseCoverage E.env "NativeD" (branches first second)
coverage first second = record
  { ctor-covered = λ {name} → covered-ctor first second {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }

-- A constant FUNCTION type motive tests capture below its own lambda.
function-type : Term
function-type = tm-pi unrestricted tm-atom_type tm-atom_type
capture-motive : Term
capture-motive = tm-lam unrestricted tm-atom_type
  (tm-lam unrestricted (tm-type l0) (tm-lam unrestricted (tm-var 0)
    (tm-lam unrestricted E.scrutinee-domain function-type)))
capture-motive-typed : E.caller ⊢ capture-motive
  ⇒ Native.motiveType E.family (tm-atom_type ∷ []) l0
capture-motive-typed = ⇒-lam ⇒-atom_type (⇐-lam (⇒-type refl)
  (⇐-lam (⇒-var Fin.zero) (⇐-lam E.fresh-kind (E.check (⇒-pi ⇒-atom_type ⇒-atom_type)))))
capture-motive-scoped : Scoped 1 capture-motive
capture-motive-scoped = sc-lam sc-atom_type
  (sc-lam sc-type (sc-lam (sc-var (Data.Nat.s≤s Data.Nat.z≤n))
    (sc-lam E.scrutinee-scoped (sc-pi sc-atom_type sc-atom_type))))
capture-path : ∀ x B y s → _⇝*_ E.sig
  (Native.apps capture-motive (x ∷ B ∷ y ∷ s ∷ [])) function-type
capture-path x B y s = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
capture-equal : ∀ x B y s → Conversion._≈_ E.conv
  (Native.apps capture-motive (x ∷ B ∷ y ∷ s ∷ [])) function-type
capture-equal x B y s = E.path-converts (capture-path x B y s)
capture-check : ∀ {name x}
  → E.Fresh E.caller ⊢ tm-lam unrestricted tm-atom_type (tm-var 4)
      ⇐ Native.apps capture-motive
        (x ∷ tm-var 1 ∷ tm-var 0 ∷ tm-ctor name (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []) ∷ [])
capture-check {name} {x} = ⇐-conv
  (⇐-lam ⇒-atom_type
    (E.check (⇒-var (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))
  (Conversion.≈-sym E.conv
    {t = Native.apps capture-motive
      (x ∷ tm-var 1 ∷ tm-var 0 ∷ tm-ctor name (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []) ∷ [])}
    {u = function-type}
    (capture-equal x (tm-var 1) (tm-var 0)
      (tm-ctor name (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []))))
capture-body : Term
capture-body = tm-lam unrestricted tm-atom_type (tm-var 4)
capture-branches : Branches E.caller E.family (tm-atom_type ∷ []) capture-motive
  (branches capture-body capture-body)
capture-branches = br∷ refl refl E.fresh-opening (E.fresh-wf E.caller-wf) capture-check
  (br∷ refl refl E.fresh-opening (E.fresh-wf E.caller-wf) capture-check br[])
capture-source : V.SourceCase E.caller "NativeComputed" (tm-atom_type ∷ []) E.fields
  capture-motive (branches capture-body capture-body)
capture-source = record
  { family = E.family ; ctor = E.computed ; found = refl ; caller = E.caller-wf
  ; parameters = E.actual-parameters ; arguments = E.actual-fields
  ; result-indices = sp∷
      (E.check (⇒-app (⇒-lam ⇒-atom_type (E.check (⇒-var Fin.zero))) ⇒-atom_lit))
      (sp∷ (E.check ⇒-float_type) (sp∷ (E.check ⇒-float_lit) sp[]))
  ; level = l0 ; motive-valid = motive capture-motive-scoped E.motive-kind capture-motive-typed
  ; branches = capture-branches ; coverage = coverage capture-body capture-body }
capture-program : Term
capture-program = tm-case (tm-ctor "NativeComputed" E.fields) capture-motive
  (branches capture-body capture-body)
capture-preserved :
  (E.caller ⊢ capture-program ⇐ function-type)
  × _⇝_ E.sig capture-program (tm-lam unrestricted tm-atom_type (tm-var 1))
  × P.T.Check E.caller (tm-lam unrestricted tm-atom_type (tm-var 1)) function-type
capture-preserved = V.preserve-selected-at capture-source
  (tt , tt , tt , tt) Frames.fields-final (tt , tt) refl
  (capture-equal
    (F.instantiateResult (tm-atom_type ∷ []) E.fields E.computed-index)
    tm-float_type tm-float_lit (tm-ctor "NativeComputed" E.fields))

-- The unused branch really contains a native whole case, outside the
-- transport fragment. The selected ordinary branch still preserves.
fresh-fields : List Term
fresh-fields = tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []
fresh-spine : Spine (E.Fresh ⟨⟩) (tm-atom_type ∷ []) fresh-fields E.indices
fresh-spine = sp∷ (E.check (⇒-var (Fin.suc (Fin.suc Fin.zero))))
  (sp∷ (E.check (⇒-var (Fin.suc Fin.zero))) (sp∷ (E.check (⇒-var Fin.zero)) sp[]))
nested : Term
nested = tm-case (tm-ctor "NativeMk" fresh-fields) E.motive-term E.branches
nested-typed : E.Fresh ⟨⟩ ⊢ nested ⇒ tm-var 1
nested-typed = ⇒-conv
  (⇒-case (E.fresh-wf wf[]) refl (⇒-ctor refl E.actual-parameters fresh-spine)
    E.actual-parameters fresh-spine E.motive-valid (E.branches-typed (E.fresh-wf wf[])) E.coverage)
  (E.motive-reduces (tm-var 2) (tm-var 1) (tm-var 0) (tm-ctor "NativeMk" fresh-fields))
mixed-branches : Branches ⟨⟩ E.family (tm-atom_type ∷ []) E.motive-term
  (branches (tm-var 0) nested)
mixed-branches = br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
  (⇐-infer (⇒-var Fin.zero)
    (E.motive-symmetric (tm-var 2) (tm-var 1) (tm-var 0) (tm-ctor "NativeMk" fresh-fields)))
  (br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
    (⇐-infer nested-typed
      (E.motive-symmetric (F.specializeParameters 3 (tm-atom_type ∷ []) E.computed-index)
        (tm-var 1) (tm-var 0) (tm-ctor "NativeComputed" fresh-fields))) br[])
mixed-source : V.SourceCase ⟨⟩ "NativeMk" (tm-atom_type ∷ []) E.fields E.motive-term
  (branches (tm-var 0) nested)
mixed-source = record
  { family = E.family ; ctor = E.mk ; found = refl ; caller = wf[]
  ; parameters = E.actual-parameters ; arguments = E.actual-fields ; result-indices = E.actual-fields
  ; level = l0 ; motive-valid = E.motive-valid ; branches = mixed-branches
  ; coverage = coverage (tm-var 0) nested }
mixed-program : Term
mixed-program = tm-case E.value E.motive-term (branches (tm-var 0) nested)
mixed-preserved :
  (⟨⟩ ⊢ mixed-program ⇐ tm-float_type)
  × _⇝_ E.sig mixed-program tm-float_lit
  × P.T.Check ⟨⟩ tm-float_lit tm-float_type
mixed-preserved = V.preserve-selected-at mixed-source
  (tt , tt , tt , tt) Frames.fields-final tt refl
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)
all-branch-support-rejected : P.SupportedBranches mixed-branches → ⊥
all-branch-support-rejected (ordinary , nested , rest) = nested
selected-nested-support-rejected : P.SelectedSupport "NativeComputed" mixed-branches → ⊥
selected-nested-support-rejected nested = nested

-- An unsupported first duplicate cannot borrow support or the body from
-- the later, supported NativeMk branch.
duplicate-branches : Branches ⟨⟩ E.family (tm-atom_type ∷ []) E.motive-term
  (("NativeMk" , 3 , nested) ∷ E.branches)
duplicate-branches = br∷ refl refl E.fresh-opening (E.fresh-wf wf[])
  (⇐-infer nested-typed
    (E.motive-symmetric (tm-var 2) (tm-var 1) (tm-var 0) (tm-ctor "NativeMk" fresh-fields)))
  (E.branches-typed wf[])
duplicate-support-rejected : P.SelectedSupport "NativeMk" duplicate-branches → ⊥
duplicate-support-rejected selected = selected
later-body-lookup-rejected : findBranch "NativeMk" (("NativeMk" , 3 , nested) ∷ E.branches)
  ≡ just ("NativeMk" , 3 , tm-var 0) → ⊥
later-body-lookup-rejected ()
