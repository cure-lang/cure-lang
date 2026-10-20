------------------------------------------------------------------------
-- Parameter-specialised SELECTED-branch contraction.
-- This proves typed substitution of a locally checked branch body and
-- exhibits its raw iota step. It does NOT type the whole source case:
-- fresh branch contexts, motive/index agreement and coverage still need
-- integration with the unified dependent typing judgment.
------------------------------------------------------------------------
module Proof.DependentBranch where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv; ctor-args)
open import Core.Reduction
open import Core.Typing using (Ctx; Conversion)
import Core.LocalFrame as F
open import Proof.LocalFrame using (staged-contraction)
open import Proof.Progress using (Final; FinalTerms; ft[]; ft∷; f-var; BuiltinCtors; Certified)
open import Proof.Preservation using (ClosedFragmentSig; ReduceConv; CertifiedTyped)
import Proof.FinalPreservation as Finality
import Proof.DependentRegistry as Registry

find-head : ∀ name ar body tail
  → findBranch name ((name , ar , body) ∷ tail) ≡ just (name , ar , body)
find-head name ar body tail with name ≟ name
... | yes refl = refl
... | no unequal = ⊥-elim (unequal refl)

push-final : ∀ {x σ} → Final x → Finality.FinalSub σ → Finality.FinalSub (F.push x σ)
push-final final finals zero = final
push-final final finals (suc i) = finals i
advance-final : ∀ {xs σ}
  → FinalTerms xs → Finality.FinalSub σ → Finality.FinalSub (F.advance xs σ)
advance-final ft[] finals = finals
advance-final (ft∷ final rest) finals = advance-final rest (push-final final finals)

specialize-final : ∀ ar {parameters body}
  → FinalTerms parameters → Final body → Final (F.specializeParameters ar parameters body)
specialize-final ar parameters final =
  Finality.substS-final _
    (Finality.extSub^-final ar (advance-final parameters (λ i → f-var))) final

module Contract (base : IndEnv) (sig : Signature) (conv : Conversion) (registry : IndEnv)
  (closed : ClosedFragmentSig base sig) (rc : ReduceConv sig conv)
  (typed : CertifiedTyped base sig conv) (bc : BuiltinCtors base) (cert : Certified sig) where
  module L = Registry.Layer base sig conv registry
  module A = L.Admission closed rc typed bc cert
  module I = A.K.I
  module P = A.P
  open Core.Typing.Typing base sig conv

  declaration : ∀ {n} {Γ : Ctx n} {name ps args} (app : L.Application Γ name ps args)
    → L.ConstructorDeclaration (L.Application.family app) (L.Application.ctor app)
  declaration app = L.constructor-declared (L.Application.registry-valid app) (L.Application.found app)

  arity : ∀ {n} {Γ : Ctx n} {name ps args} → L.Application Γ name ps args → ℕ
  arity app = length (ctor-args (L.Application.ctor app))

  runtime-body : ∀ {n} {Γ : Ctx n} {name ps args}
    → L.Application Γ name ps args → Term → Term
  runtime-body {ps = ps} app body = F.specializeParameters (arity app) ps body

  runtime-agreement : ∀ {n} {Γ : Ctx n} {name ps args}
    → (app : L.Application Γ name ps args) → ∀ body
    → substArgs args (runtime-body app body) ≡ F.instantiateResult ps args body
  runtime-agreement {ps = ps} {args = args} app body =
    trans (cong (λ ar → substArgs args (F.specializeParameters ar ps body))
      (sym (L.T.arguments-length (L.Application.fields app))))
      (staged-contraction ps args body)

  contract-typed : ∀ {n} {Γ : Ctx n} {name ps args body T}
    → (app : L.Application Γ name ps args)
    → L.ConstructorDeclaration.field-context (declaration app) ⊢ body ⇐ T
    → Γ ⊢ substArgs args (runtime-body app body) ⇐ F.instantiateResult ps args T
  contract-typed {Γ = Γ} {ps = ps} {args = args} {body = body} {T = T} app checked =
    subst (λ term → Γ ⊢ term ⇐ F.instantiateResult ps args T) (sym (runtime-agreement app body))
      (I.instantiate-result⇐
        (L.R.parameter-declarations local) (L.R.field-declarations local)
        (L.Application.parameters app) (L.Application.fields app)
        (L.Application.parameters-final app) (L.Application.fields-final app) checked)
    where
      local = L.ConstructorDeclaration.local-declaration (declaration app)

  contract-final : ∀ {n} {Γ : Ctx n} {name ps args body}
    → (app : L.Application Γ name ps args) → Final body
    → Final (substArgs args (runtime-body app body))
  contract-final app final = Finality.substArgs-final (L.Application.fields-final app)
    (specialize-final (arity app) (L.Application.parameters-final app) final)

  contract-infers : ∀ {n} {Γ : Ctx n} {name ps args body T}
    → (app : L.Application Γ name ps args) → Final body
    → L.ConstructorDeclaration.field-context (declaration app) ⊢ body ⇐ T
    → Γ ⊢ substArgs args (runtime-body app body) ⇒ F.instantiateResult ps args T
  contract-infers app final checked =
    P.check-infer (P.final-hole-free (contract-final app final)) (contract-typed app checked)

  -- Only the actual selected constructor and its declared arity are used.
  -- The motive and other branches are raw syntax here, NOT certified case
  -- typing/coverage. Whole dependent elimination remains an obligation.
  selected-step : ∀ {n} {Γ : Ctx n} {name ps args}
    → (app : L.Application Γ name ps args) → ∀ body motive tail
    → _⇝_ sig
        (tm-case (tm-ctor name args) motive ((name , arity app , runtime-body app body) ∷ tail))
        (substArgs args (runtime-body app body))
  selected-step {name = name} app body motive tail =
    ι (find-head name (arity app) (runtime-body app body) tail)
      (L.T.arguments-length (L.Application.fields app))
