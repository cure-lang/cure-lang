------------------------------------------------------------------------
-- Native constructor inversion through arbitrary conversion intermediates.
-- Only the original native constructor rule supplies the checked spines.
------------------------------------------------------------------------
module Proof.DependentConstructorInversion where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; reverse)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax
open import Core.Signature
open import Core.TypeHeads
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion; All2)
open import Core.DependentTyping
import Core.LocalFrame as F
open import Proof.DependentDataConversion using (DataComponents)

module Laws (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.DependentTyping.Typing ind sig conv
  open Conversion

  record ConstructorView {n} (Γ : Ctx n) (name : Name)
    (args : List Term) (A : Term) : Set where
    field
      family : Family
      ctor : Ctor
      parameters : List Term
      found : findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      parameters-checked : Spine Γ [] parameters (fam-params family)
      fields-checked : Spine Γ (reverse parameters) args (ctor-args ctor)
      result-conversion : _≈_ conv
        (tm-data (fam-name family) parameters
          (F.instantiateResults parameters args (ctor-indices ctor))) A
  open ConstructorView

  abstract
    data-not-sort : ∀ {name ps is l}
      → _≈_ conv (tm-data name ps is) (tm-type l) → ⊥
    data-not-sort {name} {ps} {is} {l} equal
      with ≈-heads conv {t = tm-data name ps is} {u = tm-type l}
        ty-data ty-universe equal
    ... | ()

    extend-view : ∀ {n} {Γ : Ctx n} {name args A B}
      → ConstructorView Γ name args A → _≈_ conv A B
      → ConstructorView Γ name args B
    extend-view {args = args} {A = A} {B} view equal = record
      { family = family view ; ctor = ctor view ; parameters = parameters view
      ; found = found view
      ; parameters-checked = parameters-checked view
      ; fields-checked = fields-checked view
      ; result-conversion = ≈-trans conv
          {t = tm-data (fam-name (family view)) (parameters view)
            (F.instantiateResults (parameters view) args (ctor-indices (ctor view)))}
          {u = A} {v = B} (result-conversion view) equal }

    constructor-inference : ∀ {n} {Γ : Ctx n} {name args A}
      → Γ ⊢ tm-ctor name args ⇒ A → ConstructorView Γ name args A
    constructor-inference {args = args}
      (⇒-ctor {ps = ps} {family = f} {ctor = c} lookup pars fields) =
      record
        { family = f ; ctor = c ; parameters = ps ; found = lookup
        ; parameters-checked = pars ; fields-checked = fields
        ; result-conversion = ≈-refl conv
            {t = tm-data (fam-name f) ps (F.instantiateResults ps args (ctor-indices c))} }
    constructor-inference (⇒-conv der equal) =
      extend-view (constructor-inference der) equal
    constructor-inference (⇒-cumul der le) =
      ⊥-elim (data-not-sort (result-conversion (constructor-inference der)))

    constructor-checking : ∀ {n} {Γ : Ctx n} {name args A}
      → Γ ⊢ tm-ctor name args ⇐ A → ConstructorView Γ name args A
    constructor-checking (⇐-infer der equal) =
      extend-view (constructor-inference der) equal
    constructor-checking (⇐-conv der equal) =
      extend-view (constructor-checking der) equal
    constructor-checking (⇐-cumul der le) =
      ⊥-elim (data-not-sort (result-conversion (constructor-inference der)))

  module Valid (valid : SignatureValid) where
    abstract
      owner-found : ∀ {n} {Γ : Ctx n} {name args A}
        → (view : ConstructorView Γ name args A)
        → findFamily (fam-name (family view)) (IndEnv.families ind)
          ≡ just (family view)
      owner-found view = SignatureValid.owner-visible valid (found view)

  module DataGoal (components : DataComponents conv) where
    record DataView {n} (Γ : Ctx n) (name : Name) (args : List Term)
      (target : Name) (ps is : List Term) : Set where
      field
        native : ConstructorView Γ name args (tm-data target ps is)
        family-equal : fam-name (family native) ≡ target
        parameters-convertible : All2 (_≈_ conv) (parameters native) ps
        indices-convertible : All2 (_≈_ conv)
          (F.instantiateResults (parameters native) args (ctor-indices (ctor native))) is

    abstract
      data-view : ∀ {n} {Γ : Ctx n} {name args target ps is}
        → ConstructorView Γ name args (tm-data target ps is)
        → DataView Γ name args target ps is
      data-view view with DataComponents.components components (result-conversion view)
      ... | family-eq , pars , indices = record
        { native = view ; family-equal = family-eq
        ; parameters-convertible = pars ; indices-convertible = indices }

      data-inference : ∀ {n} {Γ : Ctx n} {name args target ps is}
        → Γ ⊢ tm-ctor name args ⇒ tm-data target ps is
        → DataView Γ name args target ps is
      data-inference der = data-view (constructor-inference der)

      data-checking : ∀ {n} {Γ : Ctx n} {name args target ps is}
        → Γ ⊢ tm-ctor name args ⇐ tm-data target ps is
        → DataView Γ name args target ps is
      data-checking der = data-view (constructor-checking der)
