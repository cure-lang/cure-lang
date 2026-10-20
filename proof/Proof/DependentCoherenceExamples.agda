------------------------------------------------------------------------
-- Native coherence and exact frame transport witnesses.
-- Typed source/target examples are NOT a general native substitution or
-- preservation theorem. No closed-base preservation instance is imported.
------------------------------------------------------------------------
module Proof.DependentCoherenceExamples where

open import Data.Empty using (⊥)
open import Data.Nat using (s≤s; z≤n)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.TypeHeads
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Signature using (ctor-indices)
open import Core.Reduction using (β; substArgs)
import Core.DependentTyping
import Proof.Substitution
import Core.LocalFrame as F
import Proof.DependentTypingExamples as E
import Proof.DependentTypingControls as Controls
import Proof.DependentCoherence as Coherence
import Proof.DependentNaturality as Naturality
open import Proof.Progress
  using (Final; FinalTerms; ft[]; ft∷; f-var; f-type; f-atom_type; f-atom_lit;
         f-float_type; f-float_lit; f-app; f-lam; f-ctor)

module C = Coherence.NativeFrames E.env E.sig E.conv
open E.T

parameters-final : FinalTerms (tm-atom_type ∷ [])
parameters-final = ft∷ f-atom_type ft[]
fields-final : FinalTerms E.fields
fields-final = ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[]))
complete : C.Coherent E.Φ ⟨⟩ (F.advance E.fields (F.advance (tm-atom_type ∷ []) F.identity))
complete = C.registered-frame {name = "NativeMk"} E.valid refl
  E.actual-parameters E.actual-fields parameters-final fields-final

last-field : ⟨⟩ ⊢ tm-float_lit ⇒ tm-float_type
last-field = complete Fin.zero
type-field : ⟨⟩ ⊢ tm-float_type ⇒ tm-type l0
type-field = complete (Fin.suc Fin.zero)
first-field : ⟨⟩ ⊢ tm-atom_lit "payload" ⇒ tm-atom_type
first-field = complete (Fin.suc (Fin.suc Fin.zero))
parameter-field : ⟨⟩ ⊢ tm-atom_type ⇒ tm-type l0
parameter-field = complete (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

-- The fresh source has symbolic fields and an unrelated ambient value.
ambient-close : C.Coherent (E.Fresh E.caller) E.caller (F.advance E.fields F.identity)
ambient-close = C.branch-frame {ps = tm-atom_type ∷ []} E.fresh-opening E.actual-fields fields-final
ambient-restored : E.caller ⊢ tm-var 0 ⇒ tm-atom_type
ambient-restored = ambient-close (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
first-is-not-ambient : E.caller ⊢ tm-atom_lit "payload" ⇒ tm-atom_type
first-is-not-ambient = ambient-close (Fin.suc (Fin.suc Fin.zero))
captured-ambient : substArgs E.fields (tm-lam unrestricted tm-atom_type (tm-var 4))
  ≡ tm-lam unrestricted tm-atom_type (tm-var 1)
captured-ambient = refl

-- Open A and x are distinct caller slots, not declaration-local variables.
Γ : Ctx 2
Γ = extend E.Π (tm-var 0)
open-parameters open-arguments : List Term
open-parameters = tm-var 1 ∷ []
open-arguments = tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ []
open-parameters-checked : Spine Γ [] open-parameters E.parameters
open-parameters-checked = sp∷ (E.check (⇒-var (Fin.suc Fin.zero))) sp[]
open-arguments-checked : Spine Γ (reverse open-parameters) open-arguments E.indices
open-arguments-checked = sp∷ (E.check (⇒-var Fin.zero))
  (sp∷ (E.check ⇒-float_type) (sp∷ (E.check ⇒-float_lit) sp[]))
open-parameters-final : FinalTerms open-parameters
open-parameters-final = ft∷ f-var ft[]
open-arguments-final : FinalTerms open-arguments
open-arguments-final = ft∷ f-var (ft∷ f-float_type (ft∷ f-float_lit ft[]))
open-complete : C.Coherent E.Φ Γ (F.advance open-arguments (F.advance open-parameters F.identity))
open-complete = C.registered-frame {name = "NativeMk"} E.valid refl
  open-parameters-checked open-arguments-checked open-parameters-final open-arguments-final
open-A : Γ ⊢ tm-var 1 ⇒ tm-type l0
open-A = open-complete (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
open-x : Γ ⊢ tm-var 0 ⇒ tm-var 1
open-x = open-complete (Fin.suc (Fin.suc Fin.zero))

local-lambda : Term
local-lambda = tm-lam unrestricted (tm-var 3) (tm-var 3)
local-lambda-typed : E.Φ ⊢ local-lambda ⇒ tm-pi unrestricted (tm-var 3) (tm-var 4)
local-lambda-typed = ⇒-lam (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
  (E.check (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
open-lambda-agreement : F.instantiateResult open-parameters open-arguments local-lambda
  ≡ tm-lam unrestricted (tm-var 1) (tm-var 1)
open-lambda-agreement = refl
open-lambda-typed : Γ ⊢ tm-lam unrestricted (tm-var 1) (tm-var 1)
  ⇒ tm-pi unrestricted (tm-var 1) (tm-var 2)
open-lambda-typed = ⇒-lam (⇒-var (Fin.suc Fin.zero)) (E.check (⇒-var (Fin.suc Fin.zero)))

-- Context renaming protects the freshly added field and moves only the
-- ambient parameter; the induced substitution is natively coherent.
parameter-renaming : C.Renaming E.Π (extend E.Π tm-float_type) wk
parameter-renaming = C.weakening E.Π tm-float_type
extended-renaming : C.Renaming Γ (extend (extend E.Π tm-float_type) (tm-var 1)) (ext wk)
extended-renaming = C.extend-renaming parameter-renaming (tm-var 0)
extended-coherent : C.Coherent Γ (extend (extend E.Π tm-float_type) (tm-var 1))
  (λ i → tm-var (ext wk i))
extended-coherent = C.renaming-coherent extended-renaming

caller-substitution : Sub
caller-substitution = F.advance (tm-atom_lit "payload" ∷ [])
  (F.advance (tm-atom_type ∷ []) F.identity)
caller-coherent : C.Coherent Γ ⟨⟩ caller-substitution
caller-coherent = C.result-frame E.parameters-declared
  (dt∷ {name = "x"} (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[])
  E.actual-parameters (sp∷ (E.check ⇒-atom_lit) sp[])
  parameters-final (ft∷ f-atom_lit ft[])

computed-renaming : renameTerms wk
  (F.instantiateResults open-parameters open-arguments (ctor-indices E.computed))
  ≡ F.instantiateResults (renameTerms wk open-parameters) (renameTerms wk open-arguments)
      (ctor-indices E.computed)
computed-renaming = C.registered-results-rename {name = "NativeComputed"} E.valid refl
  open-parameters-checked open-arguments-checked wk
computed-substitution : substTermsS caller-substitution
  (F.instantiateResults open-parameters open-arguments (ctor-indices E.computed))
  ≡ F.instantiateResults (substTermsS caller-substitution open-parameters)
      (substTermsS caller-substitution open-arguments) (ctor-indices E.computed)
computed-substitution = C.registered-results-subst {name = "NativeComputed"} E.valid refl
  open-parameters-checked open-arguments-checked caller-substitution

-- A kind-correct dependent tail may require CONVERSION, not raw identity.
reducible-type : Term
reducible-type = tm-app (tm-lam unrestricted tm-atom_type tm-float_type) (tm-atom_lit "payload")
reducible-kind : ⟨⟩ ⊢ reducible-type ⇒ tm-type l0
reducible-kind = ⇒-app (⇒-lam ⇒-atom_type (E.check ⇒-float_type)) ⇒-atom_lit
converted-fields : List Term
converted-fields = tm-atom_lit "payload" ∷ reducible-type ∷ tm-float_lit ∷ []
converted-spine : Spine ⟨⟩ (tm-atom_type ∷ []) converted-fields E.indices
converted-spine = sp∷ (E.check ⇒-atom_lit) (sp∷ (E.check reducible-kind)
  (sp∷ (⇐-infer ⇒-float_lit
    (Conversion.≈-sym E.conv {t = reducible-type} {u = tm-float_type}
      (E.R.reduce-converts {t = reducible-type} {u = tm-float_type} β))) sp[]))
converted-finals : FinalTerms converted-fields
converted-finals = ft∷ f-atom_lit
  (ft∷ (f-app (f-lam f-atom_type f-float_type) f-atom_lit) (ft∷ f-float_lit ft[]))
converted-frame : C.Coherent E.Φ ⟨⟩
  (F.advance converted-fields (F.advance (tm-atom_type ∷ []) F.identity))
converted-frame = C.registered-frame {name = "NativeMk"} E.valid refl
  E.actual-parameters converted-spine parameters-final converted-finals
converted-tail-infers : ⟨⟩ ⊢ tm-float_lit ⇒ reducible-type
converted-tail-infers = converted-frame Fin.zero

-- Whole curried telescope transport applies below its binders, including
-- the final body's own binders. No typed motive transport is assumed.
curried-renaming : rename wk (Core.DependentTyping.piTele
  (F.advance open-parameters F.identity) E.indices local-lambda)
  ≡ Core.DependentTyping.piTele
      (Proof.Substitution.renameSub wk (F.advance open-parameters F.identity)) E.indices
      (rename (ext^ (length E.indices) wk) local-lambda)
curried-renaming = Naturality.rename-piTele wk (F.advance open-parameters F.identity) E.indices local-lambda
curried-substitution : substS caller-substitution (Core.DependentTyping.piTele
  (F.advance open-parameters F.identity) E.indices local-lambda)
  ≡ Core.DependentTyping.piTele
      (Proof.Substitution.substCompose caller-substitution (F.advance open-parameters F.identity)) E.indices
      (substS (extSub^ (length E.indices) caller-substitution) local-lambda)
curried-substitution = Naturality.subst-piTele caller-substitution
  (F.advance open-parameters F.identity) E.indices local-lambda

-- Registry-native types themselves occur in declaration frames. This
-- cannot be supplied by the old closed-entry base judgment.
wrapped-frame : C.Coherent (extend ⟨⟩ E.goal) ⟨⟩ (F.advance (E.value ∷ []) F.identity)
wrapped-frame = C.registered-frame {name = "NativeWrap"} E.valid refl sp[]
  (sp∷ (E.check E.value-typed) sp[]) ft[]
  (ft∷ (f-ctor fields-final) ft[])
native-scrutinee-closing : ⟨⟩ ⊢ E.value ⇒ E.goal
native-scrutinee-closing = wrapped-frame Fin.zero

-- Use the checking-mode lambda constructor, not an inferred argument
-- hidden behind ⇐-infer, when building a coherent frame.
lambda-goal lambda-argument : Term
lambda-goal = tm-pi unrestricted tm-atom_type tm-atom_type
lambda-argument = tm-lam unrestricted tm-atom_type (tm-var 0)
lambda-checked : ⟨⟩ ⊢ lambda-argument ⇐ lambda-goal
lambda-checked = ⇐-lam ⇒-atom_type (E.check (⇒-var Fin.zero))
lambda-frame : C.Coherent (extend ⟨⟩ lambda-goal) ⟨⟩
  (F.advance (lambda-argument ∷ []) F.identity)
lambda-frame = C.result-frame dt[]
  (dt∷ {name = "f"} (sc-pi sc-atom_type sc-atom_type)
    (⇒-pi ⇒-atom_type ⇒-atom_type) dt[])
  sp[] (sp∷ lambda-checked sp[]) ft[] (ft∷ (f-lam f-atom_type f-var) ft[])
lambda-inferred : ⟨⟩ ⊢ lambda-argument ⇒ lambda-goal
lambda-inferred = lambda-frame Fin.zero

-- Checking-only holes show why finality cannot be omitted from frames.
hole-checked : ⟨⟩ ⊢ tm-hole "pending" ⇐ tm-atom_type
hole-checked = ⇐-hole
hole-not-final : Final (tm-hole "pending") → ⊥
hole-not-final ()
hole-not-inferred : ∀ {T} → ⟨⟩ ⊢ tm-hole "pending" ⇒ T → ⊥
hole-not-inferred (⇒-conv der equal) = hole-not-inferred der
hole-not-inferred (⇒-cumul der le) = hole-not-inferred der
hole-not-coherent : C.Coherent (extend ⟨⟩ tm-atom_type) ⟨⟩ (topSub (tm-hole "pending")) → ⊥
hole-not-coherent coh = hole-not-inferred (coh Fin.zero)

-- Replacing y : Float with x : Atom cannot create a coherent frame.
wrong-fields : List Term
wrong-fields = tm-float_lit ∷ tm-float_type ∷ tm-atom_lit "payload" ∷ []
wrong-slot-rejected : C.Coherent E.Φ ⟨⟩
  (F.advance wrong-fields (F.advance (tm-atom_type ∷ []) F.identity)) → ⊥
wrong-slot-rejected coh
  with Conversion.≈-heads E.conv {t = tm-atom_type} {u = tm-float_type} ty-atom ty-float
    (Controls.atom-inference (coh Fin.zero))
... | ()

-- Dropping the local scope premise breaks canonical frame naturality.
unscoped-rename-rejected :
  rename wk (F.instantiateResult (tm-atom_type ∷ []) E.fields (tm-var 4))
    ≡ F.instantiateResult (tm-atom_type ∷ []) E.fields (tm-var 4) → ⊥
unscoped-rename-rejected ()
unscoped-subst-rejected :
  substTopT (tm-atom_lit "caller") (F.instantiateResult (tm-atom_type ∷ []) E.fields (tm-var 4))
    ≡ F.instantiateResult (tm-atom_type ∷ []) E.fields (tm-var 4) → ⊥
unscoped-subst-rejected ()
