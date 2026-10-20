------------------------------------------------------------------------
-- Native derivations in ONE environment/signature/conversion throughout.
-- Let-wrapped types force inversion past non-data conversion intermediates.
------------------------------------------------------------------------
module Proof.DependentConstructorInversionExamples where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l1)
open import Core.Signature using (just-inj; ctor-indices)
open import Core.TypeHeads
open import Core.Reduction using (ζ; β)
open import Core.Typing using (⟨⟩; Conversion; All2; a2[]; a2∷)
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentDataConversion as Data
import Proof.DependentConstructorInversion as Inversion

open E.T
module D = Data.Model E.sig (λ ())
module I = Inversion.Laws E.env E.sig E.conv
module G = I.DataGoal D.data-components
module V = I.Valid E.valid
open Conversion

wrap : Term → Term
wrap t = tm-let unrestricted (tm-type l1) t (tm-var 0)

computed-result computed-goal : Term
computed-result = tm-app (tm-lam unrestricted tm-atom_type (tm-var 0))
  (tm-atom_lit "payload")
computed-goal = tm-data "NativeD" (tm-atom_type ∷ [])
  (computed-result ∷ tm-float_type ∷ tm-float_lit ∷ [])

native-goal : Term
native-goal = tm-data "NativeWrapper" [] (E.value ∷ [])

abstract
  wrap-converts : ∀ t → _≈_ E.conv (wrap t) t
  wrap-converts t = E.R.reduce-converts {t = wrap t} {u = t} ζ

  unwrap-converts : ∀ t → _≈_ E.conv t (wrap t)
  unwrap-converts t =
    ≈-sym E.conv {t = wrap t} {u = t} (wrap-converts t)

  -- Two inference conversions followed by two checking conversions.
  ordinary-chain : ⟨⟩ ⊢ E.value ⇐ E.goal
  ordinary-chain = ⇐-conv {T = wrap E.goal}
    (⇐-infer {T′ = wrap (wrap E.goal)}
      (⇒-conv {T = wrap E.goal} {T′ = wrap (wrap E.goal)}
        (⇒-conv {T = E.goal} {T′ = wrap E.goal}
          E.value-typed (unwrap-converts E.goal))
        (unwrap-converts (wrap E.goal)))
      (wrap-converts (wrap E.goal)))
    (wrap-converts E.goal)

  ordinary-inverted : G.DataView ⟨⟩ "NativeMk" E.fields
    "NativeD" (tm-atom_type ∷ []) E.fields
  ordinary-inverted = G.data-checking ordinary-chain

  ordinary-owner : ∀ {A} (view : I.ConstructorView ⟨⟩ "NativeMk" E.fields A)
    → Core.Signature.findFamily
        (Core.Signature.fam-name (I.ConstructorView.family view))
        (Core.Signature.IndEnv.families E.env)
      ≡ just (I.ConstructorView.family view)
  ordinary-owner = V.owner-found

  computed-converts : _≈_ E.conv computed-goal E.goal
  computed-converts = ≈-data E.conv
    {n = "NativeD"} {ps = tm-atom_type ∷ []} {ps′ = tm-atom_type ∷ []}
    {is = computed-result ∷ tm-float_type ∷ tm-float_lit ∷ []} {is′ = E.fields}
    (a2∷ (≈-refl E.conv {t = tm-atom_type}) a2[])
    (a2∷ (E.R.reduce-converts
      {t = computed-result} {u = tm-atom_lit "payload"} β)
      (a2∷ (≈-refl E.conv {t = tm-float_type})
        (a2∷ (≈-refl E.conv {t = tm-float_lit}) a2[])))

  computed-chain : ⟨⟩ ⊢ tm-ctor "NativeComputed" E.fields ⇒ E.goal
  computed-chain = ⇒-conv {T = computed-goal} {T′ = E.goal}
    (⇒-conv {T = wrap computed-goal} {T′ = computed-goal}
      (⇒-conv {T = computed-goal} {T′ = wrap computed-goal}
        E.computed-typed (unwrap-converts computed-goal))
      (wrap-converts computed-goal))
    computed-converts

  computed-inverted : G.DataView ⟨⟩ "NativeComputed" E.fields
    "NativeD" (tm-atom_type ∷ []) E.fields
  computed-inverted = G.data-inference computed-chain

  computed-syntax-unequal : computed-goal ≡ E.goal → ⊥
  computed-syntax-unequal ()

  -- A nested registry-native constructor is a checked field, not a base
  -- literal; the same inversion traverses both wrapped type intermediates.
  native-chain : ⟨⟩ ⊢ tm-ctor "NativeWrap" (E.value ∷ []) ⇐ native-goal
  native-chain = ⇐-conv {T = wrap native-goal}
    (⇐-infer {T′ = wrap (wrap native-goal)}
      (⇒-conv {T = wrap native-goal} {T′ = wrap (wrap native-goal)}
        (⇒-conv {T = native-goal} {T′ = wrap native-goal}
          E.wrapped-typed (unwrap-converts native-goal))
        (unwrap-converts (wrap native-goal)))
      (wrap-converts (wrap native-goal)))
    (wrap-converts native-goal)

  native-inverted : G.DataView ⟨⟩ "NativeWrap" (E.value ∷ [])
    "NativeWrapper" [] (E.value ∷ [])
  native-inverted = G.data-checking native-chain

  family-conversion-rejected : _≈_ E.conv E.goal
    (tm-data "Other" (tm-atom_type ∷ []) E.fields) → ⊥
  family-conversion-rejected equal
    with Data.DataComponents.components D.data-components
      {name = "NativeD"} {other = "Other"}
      {ps = tm-atom_type ∷ []} {qs = tm-atom_type ∷ []}
      {is = E.fields} {js = E.fields} equal
  ... | () , pars , indices

  parameter-arity-rejected : _≈_ E.conv E.goal
    (tm-data "NativeD" [] E.fields) → ⊥
  parameter-arity-rejected equal
    with Data.DataComponents.components D.data-components
      {name = "NativeD"} {other = "NativeD"}
      {ps = tm-atom_type ∷ []} {qs = []}
      {is = E.fields} {js = E.fields} equal
  ... | owner , () , indices

  index-arity-rejected : _≈_ E.conv E.goal
    (tm-data "NativeD" (tm-atom_type ∷ []) []) → ⊥
  index-arity-rejected equal
    with Data.DataComponents.components D.data-components
      {name = "NativeD"} {other = "NativeD"}
      {ps = tm-atom_type ∷ []} {qs = tm-atom_type ∷ []}
      {is = E.fields} {js = []} equal
  ... | owner , pars , ()

  indices-conversion-rejected : _≈_ E.conv E.goal
    (tm-data "NativeD" (tm-atom_type ∷ [])
      (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ [])) → ⊥
  indices-conversion-rejected equal
    with Data.DataComponents.components D.data-components
      {name = "NativeD"} {other = "NativeD"}
      {ps = tm-atom_type ∷ []} {qs = tm-atom_type ∷ []}
      {is = E.fields}
      {js = tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ []} equal
  ... | owner , pars , a2∷ first (a2∷ second rest)
    with ≈-heads E.conv {t = tm-float_type} {u = tm-atom_type}
      ty-float ty-atom second
  ... | ()

  wrong-constructor-family : ∀ {ps is}
    → ⟨⟩ ⊢ E.value ⇐ tm-data "Other" ps is → ⊥
  wrong-constructor-family der with G.data-checking der
  ... | view with just-inj (I.ConstructorView.found (G.DataView.native view))
  ... | refl with G.DataView.family-equal view
  ... | ()

  missing-fields-rejected : ∀ {A}
    → ⟨⟩ ⊢ tm-ctor "NativeMk" [] ⇐ A → ⊥
  missing-fields-rejected der with I.constructor-checking der
  ... | view with just-inj (I.ConstructorView.found view)
  ... | refl with spine-length (I.ConstructorView.fields-checked view)
  ... | ()

  wrong-constructor-indices :
    ⟨⟩ ⊢ E.value ⇐ tm-data "NativeD" (tm-atom_type ∷ [])
      (tm-atom_lit "payload" ∷ tm-atom_type ∷ tm-float_lit ∷ []) → ⊥
  wrong-constructor-indices der with G.data-checking der
  ... | view with just-inj (I.ConstructorView.found (G.DataView.native view))
  ... | refl with G.DataView.indices-convertible view
  ... | a2∷ first (a2∷ second rest)
    with ≈-heads E.conv {t = tm-float_type} {u = tm-atom_type}
      ty-float ty-atom second
  ... | ()
