{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Actual fresh registry lookups, BASE-checked dependent declarations.
-- These are not inhabitants of the old full Core typing/soundness rules.
------------------------------------------------------------------------
module Proof.DependentRegistryExamples where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Signature
  using (IndEnv; Family; Ctor; fam-name; fam-ctors; ctor-name; findFamily; findCtor; just-inj)
open import Core.Typing using (⟨⟩; ∈-here)
open import Core.ClosedFragment using (ClosedFragmentSig; family-lookup-member)
open import Core.Coverage using (lookup-ctor-members)
open import Proof.Progress
  using (ft[]; ft∷; f-atom_type; f-atom_lit; f-float_type; f-float_lit; f-var)
import Proof.SoundnessModel as M
import Proof.DependentResultExamples as X
import Proof.DependentInstantiationExamples as E
import Proof.DependentSpineExamples as Earlier
import Proof.DependentRegistry as Registry

open Core.Typing.Typing M.env M.sig M.conv

family : Family
family = record X.family { fam-ctors = X.ctor ∷ X.computed-ctor ∷ [] }
registry : IndEnv
registry = record { families = family ∷ [] ; builtins = λ _ → nothing }
module L = Registry.Layer M.env M.sig M.conv registry
module A = L.Admission M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final

-- Changing only the constructor table does not alter the declaration
-- telescopes, levels or result-spine checks. Repackage, do not postulate.
repackage : ∀ {ctor}
  → X.R.LocalDeclaration X.family ctor E.Π X.Φ X.Φ
  → L.R.LocalDeclaration family ctor E.Π X.Φ X.Φ
repackage local = record
  { parameter-declarations = X.R.parameter-declarations local
  ; index-declarations = X.R.index-declarations local
  ; field-declarations = X.R.field-declarations local
  ; field-levels = X.R.field-levels local
  ; result-scoping = X.R.result-scoping local
  ; uniform-parameters = X.R.uniform-parameters local
  ; result-spines = record
      { parameters-checked = X.R.parameters-checked (X.R.result-spines local)
      ; indices-checked = X.R.indices-checked (X.R.result-spines local) } }

family-declared : ∀ {name f}
  → findFamily name (IndEnv.families registry) ≡ just f → L.FamilyDeclaration f
family-declared {name} found with family-lookup-member {name = name} {fs = IndEnv.families registry} found
... | here refl = record
  { parameter-context = E.Π ; index-context = X.Φ
  ; parameters = E.parameter-declarations ; indices = X.fields-declared }
... | there ()

constructor-declared : ∀ {name f ctor}
  → findCtor name (IndEnv.families registry) ≡ just (f , ctor) → L.ConstructorDeclaration f ctor
constructor-declared {name} found
  with lookup-ctor-members {c = name} {fs = IndEnv.families registry} found
... | here refl , here refl , equal = record
  { parameter-context = E.Π ; index-context = X.Φ ; field-context = X.Φ
  ; local-declaration = repackage X.declaration }
... | here refl , there (here refl) , equal = record
  { parameter-context = E.Π ; index-context = X.Φ ; field-context = X.Φ
  ; local-declaration = repackage X.computed-declaration }
... | here refl , there (there ()) , equal
... | there () , member , equal

owner-visible : ∀ {name f ctor}
  → findCtor name (IndEnv.families registry) ≡ just (f , ctor)
  → findFamily (fam-name f) (IndEnv.families registry) ≡ just f
owner-visible {name} found
  with lookup-ctor-members {c = name} {fs = IndEnv.families registry} found
... | here refl , member , equal = refl
... | there () , member , equal

family-fresh : ∀ {name f}
  → findFamily name (IndEnv.families registry) ≡ just f
  → findFamily (fam-name f) (IndEnv.families M.env) ≡ nothing
family-fresh {name} found with family-lookup-member {name = name} {fs = IndEnv.families registry} found
... | here refl = refl
... | there ()
constructor-fresh : ∀ {name f ctor}
  → findCtor name (IndEnv.families registry) ≡ just (f , ctor)
  → findCtor (ctor-name ctor) (IndEnv.families M.env) ≡ nothing
constructor-fresh {name} found
  with lookup-ctor-members {c = name} {fs = IndEnv.families registry} found
... | here refl , here refl , equal = refl
... | here refl , there (here refl) , equal = refl
... | here refl , there (there ()) , equal
... | there () , member , equal

checked-registry : L.Registry
checked-registry = record
  { family-declared = λ {name} → family-declared {name}
  ; constructor-declared = λ {name} → constructor-declared {name}
  ; owner-visible = λ {name} → owner-visible {name}
  ; family-fresh = λ {name} → family-fresh {name}
  ; constructor-fresh = λ {name} → constructor-fresh {name} }

application : L.Application ⟨⟩ "LocalMk" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
application = record
  { registry-valid = checked-registry ; family = family ; ctor = X.ctor ; found = refl
  ; parameters = E.parameter-arguments ; fields = X.actual-fields
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[])) }
formed-result : L.Formation ⟨⟩ "LocalResult" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
formed-result = A.result-formation application

computed-application : L.Application ⟨⟩ "LocalComputed" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
computed-application = record
  { registry-valid = checked-registry ; family = family ; ctor = X.computed-ctor ; found = refl
  ; parameters = E.parameter-arguments ; fields = X.actual-fields
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[])) }
formed-computed-result : L.Formation ⟨⟩ "LocalResult" (tm-atom_type ∷ [])
  (X.computed-result ∷ tm-float_type ∷ tm-float_lit ∷ [])
formed-computed-result = A.result-formation computed-application

open-application : L.Application E.Γ "LocalMk" (tm-atom_type ∷ [])
  (tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ [])
open-application = record
  { registry-valid = checked-registry ; family = family ; ctor = X.ctor ; found = refl
  ; parameters = E.open-parameters ; fields = X.open-fields
  ; parameters-final = ft∷ f-atom_type ft[]
  ; fields-final = ft∷ f-var (ft∷ f-float_type (ft∷ f-float_lit ft[])) }
open-result : L.Formation E.Γ "LocalResult" (tm-atom_type ∷ [])
  (tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ [])
open-result = A.result-formation open-application
substituted-result : L.Formation ⟨⟩ "LocalResult" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
substituted-result = A.subst-formation {σ = topSub (tm-atom_lit "payload")} Earlier.coherent open-result

unknown-application-rejected : ∀ {ps args} → L.Application ⟨⟩ "Unknown" ps args → ⊥
unknown-application-rejected app with L.Application.found app
... | ()
unknown-formation-rejected : ∀ {ps is} → L.Formation ⟨⟩ "Unknown" ps is → ⊥
unknown-formation-rejected admitted with L.found admitted
... | ()
missing-fields-rejected : ∀ {ps} → L.Application ⟨⟩ "LocalMk" ps [] → ⊥
missing-fields-rejected app with just-inj (L.Application.found app)
... | refl with L.T.arguments-length (L.Application.fields app)
... | ()
bad-index-formation-rejected :
  L.Formation ⟨⟩ "LocalResult" (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ []) → ⊥
bad-index-formation-rejected admitted with just-inj (L.found admitted)
... | refl = X.bad-later-index-rejected record
  { parameters-checked = L.R.parameters-checked (L.spines admitted)
  ; indices-checked = L.R.indices-checked (L.spines admitted) }

-- The registry is NOT slipped into the closed-entry base hypothesis.
registry-not-closed : ClosedFragmentSig registry M.sig → ⊥
registry-not-closed closed
  with proj₁ (proj₂ (proj₂ closed)) family (here refl) ∈-here
... | sc-var ()
not-base-typing : ∀ {T}
  → ⟨⟩ ⊢ tm-data "LocalResult" (tm-atom_type ∷ [])
      (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []) ⇒ T → ⊥
not-base-typing (⇒-data () parameters indices)
not-base-typing (⇒-conv der equal) = not-base-typing der
not-base-typing (⇒-cumul der le) = not-base-typing der

-- Namespace and owner guards reject concrete malformed registries.
shadow-family : Family
shadow-family = record family { fam-name = "Nat" }
family-shadow : IndEnv
family-shadow = record { families = shadow-family ∷ [] ; builtins = λ _ → nothing }
module FamilyShadow = Registry.Layer M.env M.sig M.conv family-shadow
family-shadow-rejected : FamilyShadow.Registry → ⊥
family-shadow-rejected valid with FamilyShadow.family-fresh valid {name = "Nat"} refl
... | ()

shadow-ctor : Ctor
shadow-ctor = record X.ctor { ctor-name = "S" }
ctor-shadow : IndEnv
ctor-shadow = record
  { families = record family { fam-ctors = shadow-ctor ∷ [] } ∷ [] ; builtins = λ _ → nothing }
module CtorShadow = Registry.Layer M.env M.sig M.conv ctor-shadow
ctor-shadow-rejected : CtorShadow.Registry → ⊥
ctor-shadow-rejected valid with CtorShadow.constructor-fresh valid {name = "S"} refl
... | ()

hidden-owner : Family
hidden-owner = record family { fam-ctors = [] }
misowned : IndEnv
misowned = record { families = hidden-owner ∷ family ∷ [] ; builtins = λ _ → nothing }
module Misowned = Registry.Layer M.env M.sig M.conv misowned
misowned-rejected : Misowned.Registry → ⊥
misowned-rejected valid
  with cong fam-ctors (just-inj (Misowned.owner-visible valid {name = "LocalMk"} refl))
... | ()
