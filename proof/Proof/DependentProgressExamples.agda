------------------------------------------------------------------------
-- Every progress observation consumes native source typing and Final.
-- No endpoint typing, preservation theorem or progress callback is used.
------------------------------------------------------------------------
module Proof.DependentProgressExamples where

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Reduction
open import Core.Coverage
import Core.DependentTyping as Native
open import Proof.Progress using (Final; FinalTerms; FinalBranches)
open Final
open FinalTerms
open FinalBranches
import Proof.DependentTypingExamples as E
import Proof.DependentConstructorInversionExamples as Chains
import Proof.DependentLiteralExamples as L
import Proof.DependentProgress as NativeProgress
import Proof.DependentCanonical as NativeCanonical
import Proof.DependentConstructorInversion as NativeConstructor

module P = NativeProgress.Progress E.env E.sig E.conv
module C = NativeCanonical.Laws E.env E.sig E.conv
module I = NativeConstructor.Laws E.env E.sig E.conv
open E.T

-- Ordinary and computed dependent D cases, both passing through actual
-- let-wrapped non-data conversion intermediates.
fields-final : FinalTerms E.fields
fields-final = ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[]))
motive-final : Final E.motive-term
motive-final = f-lam f-atom_type (f-lam f-type (f-lam f-var
  (f-lam (f-data (ft∷ f-atom_type ft[])
    (ft∷ f-var (ft∷ f-var (ft∷ f-var ft[])))) f-var)))
branches-final : FinalBranches E.branches
branches-final = fb∷ f-var (fb∷ f-var fb[])
ordinary-source : ⟨⟩ ⊢ E.program ⇒ tm-float_type
ordinary-source = ⇒-conv
  (⇒-case wf[] refl
    (⇒-conv {T = Chains.wrap E.goal} {T′ = E.goal}
      (⇒-conv {T = E.goal} {T′ = Chains.wrap E.goal}
        E.value-typed (Chains.unwrap-converts E.goal)) (Chains.wrap-converts E.goal))
    E.actual-parameters E.actual-fields E.motive-valid (E.branches-typed wf[]) E.coverage)
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit E.value)
ordinary-final : Final E.program
ordinary-final = f-case (f-ctor fields-final) motive-final branches-final
ordinary-progress : P.ProgressResult E.program × P.ProgressResult E.program
ordinary-progress = P.progress⇒ ordinary-source ordinary-final ,
  P.progress⇐ (E.check ordinary-source) ordinary-final

computed-case : Term
computed-case = tm-case (tm-ctor "NativeComputed" E.fields) E.motive-term E.branches
computed-source : ⟨⟩ ⊢ computed-case ⇒ tm-float_type
computed-source = ⇒-conv
  (⇒-case wf[] refl Chains.computed-chain E.actual-parameters E.actual-fields
    E.motive-valid (E.branches-typed wf[]) E.coverage)
  (E.motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit
    (tm-ctor "NativeComputed" E.fields))
computed-final : Final computed-case
computed-final = f-case (f-ctor fields-final) motive-final branches-final
computed-progress : P.ProgressResult computed-case × P.ProgressResult computed-case
computed-progress = P.progress⇒ computed-source computed-final ,
  P.progress⇐ (E.check computed-source) computed-final

-- Function inversion must traverse a let type before recovering the Pi.
identity-type identity-term wrapped-function identity-app : Term
identity-type = tm-pi unrestricted tm-atom_type tm-atom_type
identity-term = tm-lam unrestricted tm-atom_type (tm-var 0)
wrapped-function = Chains.wrap identity-type
identity-app = tm-app identity-term (tm-atom_lit "payload")
identity-source : ⟨⟩ ⊢ identity-term ⇒ identity-type
identity-source = ⇒-conv {T = wrapped-function} {T′ = identity-type}
  (⇒-conv {T = identity-type} {T′ = wrapped-function}
    (⇒-lam ⇒-atom_type (E.check (⇒-var Fin.zero)))
    (Chains.unwrap-converts identity-type))
  (Chains.wrap-converts identity-type)
identity-canonical : NativeCanonical.Lambda identity-term
identity-canonical = C.canonical-pi identity-source c-lam
identity-check-canonical : NativeCanonical.Lambda identity-term
identity-check-canonical = C.canonical-pi⇐ (E.check identity-source) c-lam
ordinary-check-canonical : NativeCanonical.ConstructorLike E.value
ordinary-check-canonical = C.canonical-data⇐ Chains.ordinary-chain c-ctor
identity-app-source : ⟨⟩ ⊢ identity-app ⇒ tm-atom_type
identity-app-source = ⇒-app identity-source ⇒-atom_lit
identity-app-progress : P.ProgressResult identity-app × P.ProgressResult identity-app
identity-app-progress =
  P.progress⇒ identity-app-source (f-app (f-lam f-atom_type f-var) f-atom_lit) ,
  P.progress⇐ (E.check identity-app-source) (f-app (f-lam f-atom_type f-var) f-atom_lit)

-- Source-local coverage cannot be omitted, even though the branch typing
-- list itself admits an empty derivation.
missing-coverage : CaseCoverage E.env "NativeD" [] → ⊥
missing-coverage covered with ctor-covered covered {c = "NativeMk"} refl refl
... | b , ()
missing-native-coverage : ∀ {name ps is}
  → ⟨⟩ ⊢ E.value ⇒ tm-data name ps is → CaseCoverage E.env name [] → ⊥
missing-native-coverage source covered with I.constructor-inference source
... | view with ctor-covered covered {c = "NativeMk"} (I.ConstructorView.found view)
  (C.data-name (I.ConstructorView.result-conversion view))
... | b , ()
missing-case-source : ∀ {A}
  → ⟨⟩ ⊢ tm-case E.value E.motive-term [] ⇒ A → ⊥
missing-case-source (⇒-case wf found scrutinee ps is mot brs covered) =
  missing-native-coverage scrutinee covered
missing-case-source (⇒-conv source eq) = missing-case-source source
missing-case-source (⇒-cumul source le) = missing-case-source source
missing-case-check : ∀ {A}
  → ⟨⟩ ⊢ tm-case E.value E.motive-term [] ⇐ A → ⊥
missing-case-check (⇐-infer source eq) = missing-case-source source
missing-case-check (⇐-conv source eq) = missing-case-check source
missing-case-check (⇐-cumul source le) = missing-case-source source

no-closed-var : ∀ {k A} → ⟨⟩ ⊢ tm-var k ⇒ A → ⊥
no-closed-var (⇒-var ())
no-closed-var (⇒-conv source eq) = no-closed-var source
no-closed-var (⇒-cumul source le) = no-closed-var source
no-closed-var-check : ∀ {k A} → ⟨⟩ ⊢ tm-var k ⇐ A → ⊥
no-closed-var-check (⇐-infer source eq) = no-closed-var source
no-closed-var-check (⇐-conv source eq) = no-closed-var-check source
no-closed-var-check (⇐-cumul source le) = no-closed-var source

module Literals where
  module LP = NativeProgress.Progress L.env L.sig L.conv
  nat-source : ∀ k → L.T._⊢_⇒_ ⟨⟩
    (tm-case (tm-nat_lit k) L.nat-motive L.nat-branches)
    (Native.apps L.nat-motive (tm-nat_lit k ∷ []))
  nat-source k = L.T.⇒-case L.T.wf[] refl (L.nat-chain k) L.T.sp[] L.T.sp[]
    L.nat-motive-valid L.nat-branches-valid L.nat-coverage
  bounded-source : ∀ k → L.T._⊢_⇒_ ⟨⟩
    (tm-case (tm-bounded_lit k) L.bounded-motive L.bounded-branches)
    (Native.apps L.bounded-motive (tm-bounded_lit k ∷ []))
  bounded-source k = L.T.⇒-case L.T.wf[] refl (L.bounded-chain k) L.T.sp[] L.T.sp[]
    L.bounded-motive-valid L.bounded-branches-valid L.bounded-coverage
  nat-final : ∀ k → Final (tm-case (tm-nat_lit k) L.nat-motive L.nat-branches)
  nat-final k = f-case f-nat_lit (f-lam (f-data ft[] ft[]) f-float_type)
    (fb∷ f-float_lit (fb∷ f-float_lit fb[]))
  bounded-final : ∀ k → Final (tm-case (tm-bounded_lit k) L.bounded-motive L.bounded-branches)
  bounded-final k = f-case f-bounded_lit (f-lam (f-data ft[] ft[]) f-float_type)
    (fb∷ f-float_lit (fb∷ f-float_lit fb[]))
  nat-results : ∀ k
    → LP.ProgressResult (tm-case (tm-nat_lit k) L.nat-motive L.nat-branches)
      × LP.ProgressResult (tm-case (tm-nat_lit k) L.nat-motive L.nat-branches)
  nat-results k = LP.progress⇒ (nat-source k) (nat-final k) ,
    LP.progress⇐ (L.check (nat-source k)) (nat-final k)
  bounded-results : ∀ k
    → LP.ProgressResult (tm-case (tm-bounded_lit k) L.bounded-motive L.bounded-branches)
      × LP.ProgressResult (tm-case (tm-bounded_lit k) L.bounded-motive L.bounded-branches)
  bounded-results k = LP.progress⇒ (bounded-source k) (bounded-final k) ,
    LP.progress⇐ (L.check (bounded-source k)) (bounded-final k)
  nat-zero-results = nat-results 0
  nat-suc-results = nat-results 8
  bounded-zero-results = bounded-results 0
  bounded-suc-results = bounded-results 8

module Globals where
  -- Opaque and defined globals use one signature and one native judgment.
  sig : Signature
  sig = record
    { type-of = λ _ → just tm-atom_type
    ; body = λ name → if-defined name }
    where
      if-defined : Name → Data.Maybe.Maybe Term
      if-defined name with name ≟ "defined"
      ... | yes same = just (tm-atom_lit "payload")
      ... | no different = nothing
  module G = Native.Typing E.env sig E.conv
  module GP = NativeProgress.Progress E.env sig E.conv
  opaque-source : G._⊢_⇒_ ⟨⟩ (tm-global "opaque") tm-atom_type
  opaque-source = G.⇒-global refl
  opaque-progress : GP.ProgressResult (tm-global "opaque")
  opaque-progress = GP.progress⇒ opaque-source f-global
  opaque-is-neutral : opaque-progress ≡ Data.Sum.inj₁ (neutral n-global)
  opaque-is-neutral = refl
  defined-source : G._⊢_⇒_ ⟨⟩ (tm-global "defined") tm-atom_type
  defined-source = G.⇒-global refl
  defined-progress : GP.ProgressResult (tm-global "defined")
  defined-progress = GP.progress⇒ defined-source f-global
  defined-unfolds : defined-progress ≡ Data.Sum.inj₂ (tm-atom_lit "payload" , δ refl)
  defined-unfolds = refl
