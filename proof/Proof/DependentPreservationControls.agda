------------------------------------------------------------------------
-- The new literal-layout premise excludes the checked boundary audit.
-- Rejection concerns actual registered metadata, not a typing callback.
------------------------------------------------------------------------
module Proof.DependentPreservationControls where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature
import Proof.DependentLiteralBoundaryAudit as Audit
open import Proof.DependentLiteralPreservation
  using (BuiltinShapes; NatShape; ConstructorShape)

wrong-successor-field : ∀ {ctor binder}
  → findCtor "S" (IndEnv.families Audit.env) ≡ just (Audit.family , ctor)
  → ctor-args ctor ≡ (binder , tm-data "Nat" [] []) ∷ [] → ⊥
wrong-successor-field found fields with just-inj found
... | refl with fields
... | ()

bad-layout-rejected : BuiltinShapes Audit.env → ⊥
bad-layout-rejected shapes =
  wrong-successor-field (ConstructorShape.found successor) (ConstructorShape.fields successor)
  where
    layout = BuiltinShapes.nat-shape shapes refl refl refl refl
    successor = NatShape.suc-shape layout
