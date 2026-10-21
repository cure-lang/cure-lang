{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- ACTIVE exact-arity, CLOSED-entry branch typing and preservation.
-- Next(Nat, Bounded) distinguishes both values AND types at the two slots.
-- This is not indexed-Bounded or erased-slot implementation refinement.
------------------------------------------------------------------------
module Proof.FieldOrderExamples where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Signature using (IndEnv; ctor-args; fam-name; findCtor)
open import Core.Reduction
open import Core.Coverage
open import Core.TypeHeads using (ty-data; ty-universe)
open import Core.Typing using (Ctx; Conversion; ⟨⟩; extend; lookup; branch-context)
import Proof.SoundnessModel as M
open import Proof.Progress

open Core.Typing.Typing M.env M.sig M.conv

B-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ M.B ⇒ tm-type l0
B-kind = ⇒-data refl ⊢*[] ⊢*[]

branches : Term → Term → List Branch
branches first next = ("First" , 1 , first) ∷ ("Next" , 2 , next) ∷ []

constructor-coverage : ∀ first next {c f ct}
  → findCtor c (IndEnv.families M.env) ≡ just (f , ct)
  → fam-name f ≡ "Bounded"
  → HasBranch c (Data.List.length (ctor-args ct)) (branches first next)
constructor-coverage first next {c} {f} {ct} found owner
  with lookup-ctor-members {c = c} {fs = IndEnv.families M.env} {f = f} {ct = ct} found
constructor-coverage first next found () | here refl , member , name
... | there (here refl) , here refl , refl = first , refl
... | there (here refl) , there (here refl) , refl = next , refl
... | there (here refl) , there (there ()) , name
... | there (there ()) , member , name

coverage : ∀ first next → CaseCoverage M.env "Bounded" (branches first next)
coverage first next = record
  { ctor-covered = constructor-coverage first next
  ; nat-zero-covered = λ ()
  ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ _ → first , refl
  ; bounded-suc-covered = λ _ → next , refl }

motive : Term
motive = tm-lam unrestricted M.B M.B
motive-typed : ⟨⟩ ⊢ motive ⇒ tm-pi unrestricted M.B (tm-type l0)
motive-typed = ⇒-lam B-kind (⇐-infer B-kind (M.eq-refl {tm-type l0}))

motive-contracts : ∀ a → Conversion._≈_ M.conv (tm-app motive a) M.B
motive-contracts a = M.rc {t = tm-app motive a} {t′ = M.B} β
motive-goal : ∀ a → Conversion._≈_ M.conv M.B (tm-app motive a)
motive-goal a = Conversion.≈-sym M.conv
  {t = tm-app motive a} {u = M.B} (motive-contracts a)

typed-branches : ⟨⟩ ⊢*brs branches (tm-bounded_lit 0) (tm-var 0) ⇐*ᵇ ("Bounded" , motive)
typed-branches =
  brs∷ refl (⇐-infer (⇒-bounded_lit refl) (motive-goal (tm-ctor "First" (tm-var 0 ∷ []))))
    (brs∷ refl (⇐-infer (⇒-var Fin.zero)
      (motive-goal (tm-ctor "Next" (tm-var 1 ∷ tm-var 0 ∷ [])))) brs[])

program : Term
program = tm-case (tm-bounded_lit 8) motive (branches (tm-bounded_lit 0) (tm-var 0))
program-typed : ⟨⟩ ⊢ program ⇒ M.B
program-typed = ⇒-conv
  (⇒-case (⇒-bounded_lit refl) motive-typed typed-branches (coverage _ _))
  (motive-contracts (tm-bounded_lit 8))
program-final : Final program
program-final = f-case f-bounded_lit (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
  (fb∷ f-bounded_lit (fb∷ f-var fb[]))

last-field-step : _⇝_ M.sig program (tm-bounded_lit 7)
last-field-step = ι-bounded-suc refl refl
last-field-preserved : ⟨⟩ ⊢ tm-bounded_lit 7 ⇒ M.B
last-field-preserved = M.P.preservation⇒ program-final program-typed last-field-step

fields : List Term
fields = tm-nat_lit 7 ∷ tm-bounded_lit 7 ∷ []
last-value : substArgs fields (tm-var 0) ≡ tm-bounded_lit 7
last-value = refl
first-value : substArgs fields (tm-var 1) ≡ tm-nat_lit 7
first-value = refl

Δ : Ctx 2
Δ = branch-context ⟨⟩ (ctor-args M.next)
last-type : lookup Δ Fin.zero ≡ M.B
last-type = refl
first-type : lookup Δ (Fin.suc Fin.zero) ≡ M.N
first-type = refl

wrong-slot-infer : ∀ {t T} → Δ ⊢ t ⇒ T → t ≡ tm-var 1 → Conversion._≈_ M.conv T M.B → ⊥
wrong-slot-infer (⇒-var Fin.zero) () eq
wrong-slot-infer (⇒-var (Fin.suc Fin.zero)) refl eq
  with Conversion.≈-heads M.conv ty-data ty-data eq
... | ()
wrong-slot-infer (⇒-var (Fin.suc (Fin.suc ()))) same eq
wrong-slot-infer (⇒-conv {T = T} {T′ = T′} der eq′) same eq =
  wrong-slot-infer der same (Conversion.≈-trans M.conv {t = T} {u = T′} {v = M.B} eq′ eq)
wrong-slot-infer (⇒-cumul der le) same eq
  with Conversion.≈-heads M.conv ty-universe ty-data eq
... | ()
wrong-slot-infer ⇒-atom_type () eq
wrong-slot-infer ⇒-int_type () eq
wrong-slot-infer ⇒-float_type () eq
wrong-slot-infer ⇒-binary_type () eq
wrong-slot-infer (⇒-type level) () eq
wrong-slot-infer (⇒-pi domain codomain) () eq
wrong-slot-infer (⇒-lam domain codomain) () eq
wrong-slot-infer (⇒-app function argument) () eq
wrong-slot-infer (⇒-let ty value body) () eq
wrong-slot-infer (⇒-global found) () eq
wrong-slot-infer (⇒-data found parameters indices) () eq
wrong-slot-infer (⇒-ctor found arguments) () eq
wrong-slot-infer (⇒-case scrutinee motive branches covered) () eq
wrong-slot-infer (⇒-nat_lit found) () eq
wrong-slot-infer (⇒-bounded_lit found) () eq
wrong-slot-infer ⇒-int_lit () eq
wrong-slot-infer ⇒-float_lit () eq
wrong-slot-infer ⇒-atom_lit () eq
wrong-slot-infer (⇒-effect_type ty) () eq
wrong-slot-infer (⇒-effect_pure value) () eq
wrong-slot-infer (⇒-effect_bind action continuation) () eq

wrong-slot-rejected : Δ ⊢ tm-var 1 ⇐ M.B → ⊥
wrong-slot-rejected checked =
  wrong-slot-infer (M.P.check-infer (λ name ()) checked) refl (M.eq-refl {M.B})

ordinary-program : Term
ordinary-program = tm-case (tm-ctor "Next" fields) motive (branches (tm-bounded_lit 0) (tm-var 0))
ordinary-typed : ⟨⟩ ⊢ ordinary-program ⇒ M.B
ordinary-typed = ⇒-conv
  (⇒-case (⇒-ctor refl
    (⊢*∷ (⇐-infer (⇒-nat_lit refl) (M.eq-refl {M.N}))
      (⊢*∷ (⇐-infer (⇒-bounded_lit refl) (M.eq-refl {M.B})) ⊢*[])))
    motive-typed typed-branches (coverage _ _))
  (motive-contracts (tm-ctor "Next" fields))
ordinary-preserved : ⟨⟩ ⊢ tm-bounded_lit 7 ⇒ M.B
ordinary-preserved = M.P.preservation⇒
  (f-case (f-ctor (ft∷ f-nat_lit (ft∷ f-bounded_lit ft[])))
    (f-lam (f-data ft[] ft[]) (f-data ft[] ft[])) (fb∷ f-bounded_lit (fb∷ f-var fb[])))
  ordinary-typed (ι refl refl)

weakened-typed : extend ⟨⟩ tm-atom_type ⊢ rename wk program ⇒ M.B
weakened-typed = M.P.weaken⇒ {S = tm-atom_type} program-typed

function-type lambda-motive first-lambda next-lambda lambda-program : Term
function-type = tm-pi unrestricted tm-atom_type M.B
lambda-motive = tm-lam unrestricted M.B function-type
first-lambda = tm-lam unrestricted tm-atom_type (tm-bounded_lit 0)
next-lambda = tm-lam unrestricted tm-atom_type (tm-var 1)
lambda-program = tm-case (tm-bounded_lit 8) lambda-motive (branches first-lambda next-lambda)

lambda-contracts : ∀ a → Conversion._≈_ M.conv (tm-app lambda-motive a) function-type
lambda-contracts a = M.rc {t = tm-app lambda-motive a} {t′ = function-type} β
lambda-goal : ∀ a → Conversion._≈_ M.conv function-type (tm-app lambda-motive a)
lambda-goal a = Conversion.≈-sym M.conv
  {t = tm-app lambda-motive a} {u = function-type} (lambda-contracts a)

lambda-typed : ⟨⟩ ⊢ lambda-program ⇒ function-type
lambda-typed = ⇒-conv
  (⇒-case (⇒-bounded_lit refl)
    (⇒-lam {c = tm-type l0} B-kind (⇐-infer (⇒-pi ⇒-atom_type B-kind) (M.eq-refl {tm-type l0})))
    (brs∷ refl
      (⇐-infer (⇒-lam {c = M.B} ⇒-atom_type (⇐-infer (⇒-bounded_lit refl) (M.eq-refl {M.B})))
        (lambda-goal (tm-ctor "First" (tm-var 0 ∷ []))))
      (brs∷ refl
        (⇐-infer (⇒-lam {c = M.B} ⇒-atom_type (⇐-infer (⇒-var (Fin.suc Fin.zero)) (M.eq-refl {M.B})))
          (lambda-goal (tm-ctor "Next" (tm-var 1 ∷ tm-var 0 ∷ [])))) brs[]))
    (coverage _ _))
  (lambda-contracts (tm-bounded_lit 8))

lambda-final : Final lambda-program
lambda-final = f-case f-bounded_lit
  (f-lam (f-data ft[] ft[]) (f-pi f-atom_type (f-data ft[] ft[])))
  (fb∷ (f-lam f-atom_type f-bounded_lit) (fb∷ (f-lam f-atom_type f-var) fb[]))

lambda-preserved :
  ⟨⟩ ⊢ tm-lam unrestricted tm-atom_type (tm-bounded_lit 7) ⇒ function-type
lambda-preserved = M.P.preservation⇒ lambda-final lambda-typed (ι-bounded-suc refl refl)
