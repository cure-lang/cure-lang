------------------------------------------------------------------------
-- Negative interface controls, using native derivations only.
-- The small syntax inversions below expose conversion wrappers; they are
-- not native substitution, preservation or executable refinement proofs.
------------------------------------------------------------------------
module Proof.DependentTypingControls where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Grade using (unrestricted)
open import Core.Universe using (Level; l0; l2)
open import Core.Signature
open import Core.Coverage
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.DependentTyping
import Proof.DependentTypingExamples as E
open E.T
import Proof.DependentTypingInversion as Inversion
import Proof.DependentMotiveControls as Motives
open Inversion.Laws E.env E.sig E.conv public
open Motives.Controls E.conv public
open Conversion

abstract
  unknown-family : ∀ {n} {Γ : Ctx n} {ps is A} → Γ ⊢ tm-data "Unknown" ps is ⇒ A → ⊥
  unknown-family (⇒-data () ps is)
  unknown-family (⇒-conv der equal) = unknown-family der
  unknown-family (⇒-cumul der le) = unknown-family der
  unknown-ctor : ∀ {n} {Γ : Ctx n} {args A} → Γ ⊢ tm-ctor "Unknown" args ⇒ A → ⊥
  unknown-ctor (⇒-ctor () ps args)
  unknown-ctor (⇒-conv der equal) = unknown-ctor der
  unknown-ctor (⇒-cumul der le) = unknown-ctor der

  type2-not-inferred : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ tm-type l2 ⇒ A → ⊥
  type2-not-inferred (⇒-type ())
  type2-not-inferred (⇒-conv der equal) = type2-not-inferred der
  type2-not-inferred (⇒-cumul der le) = type2-not-inferred der
  bad-declaration : ∀ {m} {Δ : Ctx m} → Declared ⟨⟩ (("bad" , tm-type l2) ∷ []) Δ → ⊥
  bad-declaration (dt∷ scope kind rest) = type2-not-inferred kind
  forward-reference : ∀ {m} {Δ : Ctx m} → Declared ⟨⟩ (("bad" , tm-var 0) ∷ []) Δ → ⊥
  forward-reference (dt∷ (sc-var ()) kind rest)
  too-small-field-budget : LevelsBelow l0 E.indices-declared → ⊥
  too-small-field-budget (first , () , rest)

  bad-parameter : Spine ⟨⟩ [] (tm-atom_lit "not-a-type" ∷ []) E.parameters → ⊥
  bad-parameter (sp∷ checked rest) = atom-not-sort (atom-checking checked)
  bad-dependent-index : Spine ⟨⟩ (tm-atom_type ∷ [])
    (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ []) E.indices → ⊥
  bad-dependent-index (sp∷ first (sp∷ second (sp∷ third rest)))
    with ≈-heads E.conv {t = tm-float_type} {u = tm-atom_type} ty-float ty-atom (float-checking third)
  ... | ()
  missing-fields : ∀ {locals} → Spine ⟨⟩ locals [] E.indices → ⊥
  missing-fields ()
  nonuniform-parameters : Core.Signature.ctor-params
    (record E.mk { ctor-params = tm-atom_type ∷ [] })
    ≡ parameterSlots 3 1 → ⊥
  nonuniform-parameters ()

  missing-coverage : CaseCoverage E.env "NativeD" [] → ⊥
  missing-coverage covered with ctor-covered covered {c = "NativeMk"} refl refl
  ... | body , ()
  wrong-arity-coverage : ∀ {b} →
    CaseCoverage E.env "NativeD" (("NativeMk" , 4 , b) ∷ []) → ⊥
  wrong-arity-coverage covered with ctor-covered covered {c = "NativeMk"} refl refl
  ... | body , ()
  wrong-owner : ∀ {n} {Γ : Ctx n} {ps m ar b brs}
    → Branches Γ E.family ps m (("NativeWrap" , ar , b) ∷ brs) → ⊥
  wrong-owner (br∷ found owner opening wf checked rest) with just-inj found
  ... | refl with cong fam-name owner
  ... | ()

  -- The old incoherent base closing is not smuggled into native evidence:
  -- native-closing is positive in E, while missing registration still fails.
  empty-env : IndEnv
  empty-env = record { families = [] ; builtins = λ _ → nothing }
  module Empty = Core.DependentTyping.Typing empty-env E.sig E.conv
  unregistered-goal : ∀ {n} {Γ : Ctx n} {A} → Empty._⊢_⇒_ Γ E.goal A → ⊥
  unregistered-goal (Empty.⇒-data () ps is)
  unregistered-goal (Empty.⇒-conv der equal) = unregistered-goal der
  unregistered-goal (Empty.⇒-cumul der le) = unregistered-goal der
