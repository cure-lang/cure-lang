------------------------------------------------------------------------
-- Fresh caller branch contexts, distinct from local declaration contexts.
-- Fields are opened FORWARDS with specialised types. Closing the resulting
-- context uses the actual checked fields and preserves ambient variables.
-- Motive/index agreement, coverage and unified case typing are not assumed.
------------------------------------------------------------------------
module Proof.DependentOpening where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Core.Syntax
open import Core.Signature using (IndEnv; Telescope; ctor-args)
open import Core.Reduction using (Signature; substArgs)
open import Core.Typing using (Ctx; extend; lookup; Conversion)
import Core.LocalFrame as F
open import Proof.LocalFrame using (push-undoes-wk)
open import Proof.Substitution using (subst-compose; substCompose; substS-idSub)
open import Proof.Progress using (FinalTerms; ft[]; ft∷; BuiltinCtors; Certified)
open import Proof.Preservation using (ClosedFragmentSig; ReduceConv; CertifiedTyped)
import Proof.DependentRegistry as Registry

data Opened : ∀ {n m} → Ctx n → Sub → Telescope → Ctx m → Set where
  op[] : ∀ {n} {Γ : Ctx n} {σ} → Opened Γ σ [] Γ
  op∷ : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ name T tele}
    → Opened (extend Γ (substS σ T)) (extSub σ) tele Θ
    → Opened Γ σ ((name , T) ∷ tele) Θ

opened-length : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
  → Opened Γ σ tele Θ → length tele + n ≡ m
opened-length op[] = refl
opened-length {n = n} (op∷ {tele = tele} rest) =
  trans (sym (+-suc (length tele) n)) (opened-length rest)

record Opening {n} (Γ : Ctx n) (σ : Sub) (tele : Telescope) : Set where
  field
    {size} : ℕ
    context : Ctx size
    trace : Opened Γ σ tele context

build : ∀ {n} (Γ : Ctx n) (σ : Sub) (tele : Telescope) → Opening Γ σ tele
build Γ σ [] = record { context = Γ ; trace = op[] }
build Γ σ ((name , T) ∷ tele) with build (extend Γ (substS σ T)) (extSub σ) tele
... | opened = record { context = Opening.context opened ; trace = op∷ (Opening.trace opened) }

ext-suc : ∀ n σ → extSub^ n (extSub σ) ≡ extSub^ (suc n) σ
ext-suc zero σ = refl
ext-suc (suc n) σ = cong extSub (ext-suc n σ)

-- Composing a fresh-binder substitution with a checked field push threads
-- actual fields without capturing their caller variables.
push-compose : ∀ arg τ σ locals
  → (∀ i → substCompose τ σ i ≡ F.prefix locals F.identity i)
  → ∀ i → substCompose (F.push arg τ) (extSub σ) i ≡ F.prefix (arg ∷ locals) F.identity i
push-compose arg τ σ locals equal zero = refl
push-compose arg τ σ locals equal (suc i) =
  trans (push-undoes-wk arg τ (σ i)) (equal i)

module Typed (base : IndEnv) (sig : Signature) (conv : Conversion) (registry : IndEnv)
  (closed : ClosedFragmentSig base sig) (rc : ReduceConv sig conv)
  (typed : CertifiedTyped base sig conv) (bc : BuiltinCtors base) (cert : Certified sig) where
  module L = Registry.Layer base sig conv registry
  module A = L.Admission closed rc typed bc cert
  module I = A.K.I
  module P = A.P
  open Core.Typing.Typing base sig conv

  data Kinded : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele} → Opened Γ σ tele Θ → Set where
    ok[] : ∀ {n} {Γ : Ctx n} {σ} → Kinded (op[] {Γ = Γ} {σ = σ})
    ok∷ : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ name T tele l}
      {rest : Opened (extend Γ (substS σ T)) (extSub σ) tele Θ}
      → Γ ⊢ substS σ T ⇒ tm-type l → Kinded rest
      → Kinded (op∷ {σ = σ} {name = name} {T = T} rest)

  open-coherent : ∀ {d e n m} {Δ : Ctx d} {Ε : Ctx e} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
    → L.T.Declared Δ tele Ε → Opened Γ σ tele Θ → P.Coherent Δ Γ σ
    → P.Coherent Ε Θ (extSub^ (length tele) σ)
  open-coherent L.T.dt[] op[] coh = coh
  open-coherent {Ε = Ε} {Θ = Θ} {σ = σ}
    (L.T.dt∷ {tele = tele} scoped kind declarations) (op∷ rest) coh =
    subst (P.Coherent Ε Θ) (ext-suc (length tele) σ)
      (open-coherent declarations rest (P.coh-extend coh))

  open-kinded : ∀ {d e n m} {Δ : Ctx d} {Ε : Ctx e} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
    → L.T.Declared Δ tele Ε → (opening : Opened Γ σ tele Θ) → P.Coherent Δ Γ σ → Kinded opening
  open-kinded L.T.dt[] op[] coh = ok[]
  open-kinded {σ = σ} (L.T.dt∷ {T = T} scoped kind declarations) (op∷ rest) coh =
    ok∷ {σ = σ} {T = T} (P.subst⇒ coh kind) (open-kinded declarations rest (P.coh-extend coh))

  -- This is more general than closing declaration-local bodies: Δ may
  -- contain an unrelated ambient caller context, realised by τ.
  close-coherent : ∀ {n d m} {Γ : Ctx n} {Δ : Ctx d} {Θ : Ctx m} {σ τ locals args tele}
    → Opened Δ σ tele Θ → L.T.Arguments Γ locals args tele → FinalTerms args
    → P.Coherent Δ Γ τ
    → (∀ i → substCompose τ σ i ≡ F.prefix locals F.identity i)
    → P.Coherent Θ Γ (F.advance args τ)
  close-coherent op[] L.T.as[] ft[] coh equal = coh
  close-coherent {Γ = Γ} {σ = σ} {τ = τ} {locals = locals}
    (op∷ {T = T} rest) (L.T.as∷ {arg = arg} checked arguments) (ft∷ final finals) coh equal =
    close-coherent rest arguments finals
      (I.coherent-push coh
        (subst (λ A → Γ ⊢ arg ⇒ A) (sym expected)
          (P.check-infer (P.final-hole-free final) checked)))
      (push-compose arg τ σ locals equal)
    where
      expected : substS τ (substS σ T) ≡ F.instantiatePrefix locals T
      expected = trans (subst-compose τ σ T)
        (trans (cong (λ ρ → substS ρ T) (funext equal)) (I.prefix-agrees locals T))

  identity-coherent : ∀ {n} (Γ : Ctx n) → P.Coherent Γ Γ F.identity
  identity-coherent Γ i =
    subst (λ A → Γ ⊢ tm-var (toℕ i) ⇒ A) (sym (substS-idSub (lookup Γ i))) (⇒-var i)

  declaration : ∀ {n} {Γ : Ctx n} {name ps args}
    → (app : L.Application Γ name ps args)
    → L.ConstructorDeclaration (L.Application.family app) (L.Application.ctor app)
  declaration app = L.constructor-declared (L.Application.registry-valid app) (L.Application.found app)

  branch-opening : ∀ {n} {Γ : Ctx n} {name ps args}
    → (app : L.Application Γ name ps args)
    → Opening Γ (F.advance ps F.identity) (ctor-args (L.Application.ctor app))
  branch-opening {Γ = Γ} {ps = ps} app = build Γ (F.advance ps F.identity) _

  branch-context : ∀ {n} {Γ : Ctx n} {name ps args}
    → (app : L.Application Γ name ps args) → Ctx (Opening.size (branch-opening app))
  branch-context app = Opening.context (branch-opening app)

  branch-context-size : ∀ {n} {Γ : Ctx n} {name ps args} (app : L.Application Γ name ps args)
    → length (ctor-args (L.Application.ctor app)) + n ≡ Opening.size (branch-opening app)
  branch-context-size app = opened-length (Opening.trace (branch-opening app))

  parameter-coherent : ∀ {n} {Γ : Ctx n} {name ps args} (app : L.Application Γ name ps args)
    → P.Coherent (L.ConstructorDeclaration.parameter-context (declaration app)) Γ (F.advance ps F.identity)
  parameter-coherent app = I.result-frame
    (L.R.parameter-declarations local) L.T.dt[] (L.Application.parameters app) L.T.as[]
    (L.Application.parameters-final app) ft[]
    where local = L.ConstructorDeclaration.local-declaration (declaration app)

  branch-kinded : ∀ {n} {Γ : Ctx n} {name ps args} (app : L.Application Γ name ps args)
    → Kinded (Opening.trace (branch-opening app))
  branch-kinded app = open-kinded
    (L.R.field-declarations (L.ConstructorDeclaration.local-declaration (declaration app)))
    (Opening.trace (branch-opening app)) (parameter-coherent app)

  local-to-branch : ∀ {n} {Γ : Ctx n} {name ps args body T} (app : L.Application Γ name ps args)
    → L.ConstructorDeclaration.field-context (declaration app) ⊢ body ⇐ T
    → branch-context app ⊢ F.specializeParameters (length (ctor-args (L.Application.ctor app))) ps body
        ⇐ F.specializeParameters (length (ctor-args (L.Application.ctor app))) ps T
  local-to-branch app checked = P.subst⇐
    (open-coherent (L.R.field-declarations local) (Opening.trace (branch-opening app)) (parameter-coherent app))
    checked
    where local = L.ConstructorDeclaration.local-declaration (declaration app)

  branch-coherent : ∀ {n} {Γ : Ctx n} {name ps args} (app : L.Application Γ name ps args)
    → P.Coherent (branch-context app) Γ (F.advance args F.identity)
  branch-coherent {ps = ps} app =
    close-coherent (Opening.trace (branch-opening app)) (L.Application.fields app)
      (L.Application.fields-final app) (identity-coherent _)
      (λ i → trans (substS-idSub (F.advance ps F.identity i)) (F.advance-reverse ps F.identity i))

  -- ANY body typed in the fresh caller context may close, including
  -- direct ambient-variable references absent from the local declaration.
  contract-branch : ∀ {n} {Γ : Ctx n} {name ps args body T} (app : L.Application Γ name ps args)
    → branch-context app ⊢ body ⇐ T
    → Γ ⊢ substArgs args body ⇐ substArgs args T
  contract-branch {Γ = Γ} {args = args} {body = body} {T = T} app checked =
    subst₂ (λ b A → Γ ⊢ b ⇐ A) (F.fields-agree args body) (F.fields-agree args T)
      (P.subst⇐ (branch-coherent app) checked)

  contract-branch⇒ : ∀ {n} {Γ : Ctx n} {name ps args body T} (app : L.Application Γ name ps args)
    → branch-context app ⊢ body ⇒ T
    → Γ ⊢ substArgs args body ⇒ substArgs args T
  contract-branch⇒ {Γ = Γ} {args = args} {body = body} {T = T} app checked =
    subst₂ (λ b A → Γ ⊢ b ⇒ A) (F.fields-agree args body) (F.fields-agree args T)
      (P.subst⇒ (branch-coherent app) checked)
