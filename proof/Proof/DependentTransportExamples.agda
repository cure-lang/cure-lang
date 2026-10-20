------------------------------------------------------------------------
-- These witnesses INVOKE native typing transport, rather than checking
-- the target independently. Whole-case support is explicitly rejected.
------------------------------------------------------------------------
module Proof.DependentTransportExamples where

open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Nat using (s≤s; z≤n)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Signature using (ctor-indices)
import Core.Typing
open import Core.Typing using (Ctx; ⟨⟩; extend)
open import Core.Reduction using (ζ)
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentTransport as Transport
open import Proof.Progress using (ft∷; f-atom_lit; ft[])

module T = Transport.Transport E.env E.sig E.conv
module V = T.Valid E.valid
open E.T

-- Close A and x in the ambient caller. The frame itself is obtained
-- from checked native declaration/argument spines.
caller-close : V.Coherent Frames.Γ ⟨⟩ Frames.caller-substitution
caller-close = V.result-frame E.parameters-declared
  (dt∷ {name = "x"} (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[])
  E.actual-parameters (sp∷ (E.check ⇒-atom_lit) sp[])
  (tt , tt) (tt , tt) Frames.parameters-final
  (ft∷ f-atom_lit ft[])

open-frame : V.Coherent E.Φ Frames.Γ
  (F.advance Frames.open-arguments (F.advance Frames.open-parameters F.identity))
open-frame = V.registered-frame {name = "NativeMk"} refl
  Frames.open-parameters-checked Frames.open-arguments-checked
  (tt , tt) (tt , tt , tt , tt)
  Frames.open-parameters-final Frames.open-arguments-final

-- The former checkpoint only constructed this target derivation by hand.
-- This target now comes from the native general-fragment substitution.
lambda-transported : T.Infer Frames.Γ
  (tm-lam unrestricted (tm-var 1) (tm-var 1))
  (tm-pi unrestricted (tm-var 1) (tm-var 2))
lambda-transported = V.subst⇒ open-frame Frames.local-lambda-typed (tt , tt)

checking-lambda-transported : T.Check Frames.Γ
  (tm-lam unrestricted (tm-var 1) (tm-var 1))
  (tm-pi unrestricted (tm-var 1) (tm-var 2))
checking-lambda-transported = V.subst⇐ open-frame source (tt , tt)
  where
    source : E.Φ ⊢ Frames.local-lambda ⇐ tm-pi unrestricted (tm-var 3) (tm-var 4)
    source = ⇐-lam (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
      (E.check (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

-- Computed result syntax is preserved, not silently normalised.
computed-term computed-goal : Term
computed-term = tm-ctor "NativeComputed" Frames.open-arguments
computed-goal = tm-data "NativeD" Frames.open-parameters
  (F.instantiateResults Frames.open-parameters Frames.open-arguments
    (ctor-indices E.computed))
computed-typed : Frames.Γ ⊢ computed-term ⇒ computed-goal
computed-typed = ⇒-ctor refl Frames.open-parameters-checked Frames.open-arguments-checked
computed-supported : T.Supported⇒ computed-typed
computed-supported = (tt , tt) , tt , tt , tt , tt

computed-weakened : T.Infer (extend Frames.Γ tm-atom_type)
  (rename wk computed-term) (rename wk computed-goal)
computed-weakened = V.rename⇒ (T.C.weakening Frames.Γ tm-atom_type)
  computed-typed computed-supported
computed-closed : T.Infer ⟨⟩
  (tm-ctor "NativeComputed" E.fields)
  (substS Frames.caller-substitution computed-goal)
computed-closed = V.subst⇒ caller-close computed-typed computed-supported

data-typed : Frames.Γ ⊢
  tm-data "NativeD" Frames.open-parameters Frames.open-arguments ⇒ tm-type l1
data-typed = ⇒-data refl Frames.open-parameters-checked Frames.open-arguments-checked
data-closed : T.Infer ⟨⟩ E.goal (tm-type l1)
data-closed = V.subst⇒ caller-close data-typed ((tt , tt) , tt , tt , tt , tt)

-- Here substitution images are registry-native constructors, not base
-- literals. Transport below a lambda invokes their actual weakening.
native-image : V.Coherent (extend ⟨⟩ E.goal) ⟨⟩ (topSub E.value)
native-image = V.top-coherent
  (E.value-typed , (tt , tt) , tt , tt , tt , tt)
native-wrapper-source : extend ⟨⟩ E.goal ⊢
  tm-ctor "NativeWrap" (tm-var 0 ∷ []) ⇒ tm-data "NativeWrapper" [] (tm-var 0 ∷ [])
native-wrapper-source = ⇒-ctor refl sp[] (sp∷ (E.check (⇒-var Fin.zero)) sp[])
native-wrapper-closed : T.Infer ⟨⟩
  (tm-ctor "NativeWrap" (E.value ∷ [])) (tm-data "NativeWrapper" [] (E.value ∷ []))
native-wrapper-closed = V.subst⇒ native-image native-wrapper-source (tt , tt , tt)

native-capture-source : extend ⟨⟩ E.goal ⊢
  tm-lam unrestricted tm-atom_type (tm-var 1) ⇒ tm-pi unrestricted tm-atom_type E.goal
native-capture-source = ⇒-lam ⇒-atom_type (E.check (⇒-var (Fin.suc Fin.zero)))
native-capture-closed : T.Infer ⟨⟩
  (tm-lam unrestricted tm-atom_type E.value) (tm-pi unrestricted tm-atom_type E.goal)
native-capture-closed = V.subst⇒ native-image native-capture-source (tt , tt)
native-frame-agrees : T.C.Coherent (extend ⟨⟩ E.goal) ⟨⟩ (topSub E.value)
native-frame-agrees = V.forget-coherent {Γ = extend ⟨⟩ E.goal}
  {σ = topSub E.value} native-image

-- Fresh branch contraction also uses the native substitution theorem.
-- The ambient value is unrelated to the first constructor field.
branch-ambient-source : E.Fresh E.caller ⊢ tm-var 3 ⇐ tm-atom_type
branch-ambient-source = E.check (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
branch-ambient-closed : T.Check E.caller (tm-var 0) tm-atom_type
branch-ambient-closed = V.contract-branch {ps = tm-atom_type ∷ []}
  E.fresh-opening E.actual-fields (tt , tt , tt , tt) Frames.fields-final
  branch-ambient-source tt
branch-capture-source : E.Fresh E.caller ⊢
  tm-lam unrestricted tm-atom_type (tm-var 4) ⇐ tm-pi unrestricted tm-atom_type tm-atom_type
branch-capture-source = ⇐-lam ⇒-atom_type
  (E.check (⇒-var (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))
branch-capture-closed : T.Check E.caller
  (tm-lam unrestricted tm-atom_type (tm-var 1)) (tm-pi unrestricted tm-atom_type tm-atom_type)
branch-capture-closed = V.contract-branch {ps = tm-atom_type ∷ []}
  E.fresh-opening E.actual-fields (tt , tt , tt , tt) Frames.fields-final
  branch-capture-source (tt , tt)
branch-dependent-source : E.Fresh E.caller ⊢ tm-var 0 ⇐ tm-var 1
branch-dependent-source = E.check (⇒-var Fin.zero)
branch-dependent-closed : T.Check E.caller tm-float_lit tm-float_type
branch-dependent-closed = V.contract-branch {ps = tm-atom_type ∷ []}
  E.fresh-opening E.actual-fields (tt , tt , tt , tt) Frames.fields-final
  branch-dependent-source tt

-- Support permits checking holes, but does not manufacture inference or
-- finality for them. This mirrors the existing native hole discipline.
hole-transported : T.Check ⟨⟩ (tm-hole "pending") tm-atom_type
hole-transported = V.subst⇐ (V.identity ⟨⟩) Frames.hole-checked tt
hole-still-not-inferred : ∀ {T′} → T.Infer ⟨⟩ (tm-hole "pending") T′ → ⊥
hole-still-not-inferred evidence = Frames.hole-not-inferred (proj₁ evidence)
wrong-slot-still-rejected : V.Coherent E.Φ ⟨⟩
  (F.advance Frames.wrong-fields (F.advance (tm-atom_type ∷ []) F.identity)) → ⊥
wrong-slot-still-rejected coh = Frames.wrong-slot-rejected
  (V.forget-coherent {Γ = E.Φ}
    {σ = F.advance Frames.wrong-fields (F.advance (tm-atom_type ∷ []) F.identity)} coh)

-- Even a valid native whole case is outside this transport fragment.
whole-case-excluded : T.Supported⇒ E.program-typed → ⊥
whole-case-excluded unsupported = unsupported

-- A raw case-free constructor can hide a CASE in its parameter witness.
-- The derivation-based predicate rejects it despite unchanged runtime fields.
hidden-parameter : Term
hidden-parameter = tm-let unrestricted tm-float_type E.program tm-atom_type
hidden-kind : ⟨⟩ ⊢ hidden-parameter ⇒ tm-type l0
hidden-kind = ⇒-let ⇒-float_type (E.check E.program-typed) ⇒-atom_type
hidden-parameters : Spine ⟨⟩ [] (hidden-parameter ∷ []) E.parameters
hidden-parameters = sp∷ (E.check hidden-kind) sp[]
hidden-fields : Spine ⟨⟩ (hidden-parameter ∷ []) E.fields E.indices
hidden-fields = sp∷ (⇐-infer ⇒-atom_lit
  (Core.Typing.Conversion.≈-sym E.conv
    {t = hidden-parameter} {u = tm-atom_type}
    (E.R.reduce-converts {t = hidden-parameter} {u = tm-atom_type} ζ)))
  (sp∷ (E.check ⇒-float_type) (sp∷ (E.check ⇒-float_lit) sp[]))
hidden-constructor : ⟨⟩ ⊢ E.value ⇒
  tm-data "NativeD" (hidden-parameter ∷ []) E.fields
hidden-constructor = ⇒-ctor refl hidden-parameters hidden-fields
hidden-case-excluded : T.Supported⇒ hidden-constructor → ⊥
hidden-case-excluded (((kind , unsupported , body) , rest) , fields) = unsupported
