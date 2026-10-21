------------------------------------------------------------------------
-- Local declaration validity and typed instantiation of dependent frames.
-- This bridges declaration contexts to actual caller terms, not a new
-- constructor/data admission rule or a full executable refinement.
------------------------------------------------------------------------
module Proof.DependentInstantiation where

open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (zero; suc; toℕ)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Properties using (length-reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv; Telescope)
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion; ⟨⟩; extend; lookup; lookup-extend)
import Core.LocalFrame as F
open import Core.Verification using (ScopedTele; tele[]; tele∷)
open import Proof.Progress using (BuiltinCtors; Certified; FinalTerms; ft[]; ft∷)
import Proof.LocalFrame as Local
open import Proof.Preservation
  using (ClosedFragmentSig; ReduceConv; CertifiedTyped; module Preserve)
import Proof.DependentSpine as Dependent

module Telescopes (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.Typing.Typing ind sig conv
  module D = Dependent.Spines ind sig conv

  -- Unlike extendTele, these declarations extend FORWARDS. Each next
  -- entry is scoped and kind-checked under the preceding binders.
  data Declared : ∀ {n m} → Ctx n → Telescope → Ctx m → Set where
    dt[] : ∀ {n} {Γ : Ctx n} → Declared Γ [] Γ
    dt∷ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {name T tele l}
      → Scoped n T → Γ ⊢ T ⇒ tm-type l
      → Declared (extend Γ T) tele Δ
      → Declared Γ ((name , T) ∷ tele) Δ

  declared-length : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
    → Declared Γ tele Δ → length tele + n ≡ m
  declared-length dt[] = refl
  declared-length {n = n} (dt∷ {tele = tele} scoped kind rest) =
    trans (sym (+-suc (length tele) n)) (declared-length rest)

  declared-scoping : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
    → Declared Γ tele Δ → ScopedTele n tele
  declared-scoping dt[] = tele[]
  declared-scoping (dt∷ scoped kind rest) = tele∷ scoped (declared-scoping rest)

  -- Application evidence WITHOUT entry kinds. The theorem below derives
  -- those kinds from Declared, rather than assuming them at each call.
  data Arguments {n} (Γ : Ctx n) : List Term → List Term → Telescope → Set where
    as[] : ∀ {locals} → Arguments Γ locals [] []
    as∷ : ∀ {locals arg args name T tele}
      → Γ ⊢ arg ⇐ F.instantiatePrefix locals T
      → Arguments Γ (arg ∷ locals) args tele
      → Arguments Γ locals (arg ∷ args) ((name , T) ∷ tele)

  arguments-length : ∀ {n} {Γ : Ctx n} {locals args tele}
    → Arguments Γ locals args tele → length args ≡ length tele
  arguments-length as[] = refl
  arguments-length (as∷ checked rest) = cong suc (arguments-length rest)

  forget-kinds : ∀ {n} {Γ : Ctx n} {locals args tele}
    → D.Checked Γ locals args tele → Arguments Γ locals args tele
  forget-kinds D.ds[] = as[]
  forget-kinds (D.ds∷ scoped kind checked rest) = as∷ checked (forget-kinds rest)

  module Instantiation (closed : ClosedFragmentSig ind sig) (rc : ReduceConv sig conv)
    (typed : CertifiedTyped ind sig conv) (bc : BuiltinCtors ind) (cert : Certified sig) where
    module P = Preserve ind sig conv closed rc typed bc cert

    prefix-agrees : ∀ locals T
      → substS (F.prefix locals F.identity) T ≡ F.instantiatePrefix locals T
    prefix-agrees locals T = cong (λ σ → substS σ T) (funext (F.prefix-args 0 locals))

    push-undoes-wk : ∀ arg σ T
      → substS (F.push arg σ) (rename wk T) ≡ substS σ T
    push-undoes-wk = Local.push-undoes-wk

    -- Pushing a checked final argument REALISES a declaration binder;
    -- unlike coh-extend this does not add a binder to the caller context.
    coherent-push : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ T arg}
      → P.Coherent Δ Γ σ → Γ ⊢ arg ⇒ substS σ T
      → P.Coherent (extend Δ T) Γ (F.push arg σ)
    coherent-push {σ = σ} {T = T} {arg = arg} coh checked zero =
      subst (λ A → _ ⊢ arg ⇒ A) (sym (push-undoes-wk arg σ T)) checked
    coherent-push {Δ = Δ} {σ = σ} {T = T} {arg = arg} coh checked (suc i) =
      subst (λ A → _ ⊢ σ (toℕ i) ⇒ A)
        (sym (trans (cong (substS (F.push arg σ)) (lookup-extend Δ T i))
          (push-undoes-wk arg σ (lookup Δ i)))) (coh i)

    -- Derive the old Checked judgment AND a coherent complete frame.
    -- Finality excludes checking-only holes; no Value or termination
    -- premise is smuggled into argument instantiation.
    instantiate : ∀ {n d e} {Γ : Ctx n} {Δ : Ctx d} {Ε : Ctx e} {locals args tele}
      → Declared Δ tele Ε → length locals ≡ d
      → Arguments Γ locals args tele → FinalTerms args
      → P.Coherent Δ Γ (F.prefix locals F.identity)
      → D.Checked Γ locals args tele
        × P.Coherent Ε Γ (F.advance args (F.prefix locals F.identity))
    instantiate dt[] size as[] ft[] coh = D.ds[] , coh
    instantiate {Γ = Γ} {locals = locals}
      (dt∷ {T = T} {l = l} scoped kind declarations) size
      (as∷ {arg = arg} checked arguments) (ft∷ final finals) coh
      with instantiate declarations (cong suc size) arguments finals
        (coherent-push coh
          (subst (λ A → Γ ⊢ arg ⇒ A) (sym (prefix-agrees locals T))
            (P.check-infer (P.final-hole-free final) checked)))
    ... | rest , complete =
      D.ds∷ (subst (λ d → Scoped d T) (sym size) scoped)
        (subst (λ A → Γ ⊢ A ⇒ tm-type l)
          (prefix-agrees locals T) (P.subst⇒ coh kind))
        checked rest , complete

    -- Parameters and fields are checked separately, but result bodies
    -- see BOTH, in last-field/last-parameter-first local order.
    result-frame : ∀ {n p f} {Γ : Ctx n} {Π : Ctx p} {Φ : Ctx f}
      {parameters fields parameter-tele field-tele}
      → Declared ⟨⟩ parameter-tele Π → Declared Π field-tele Φ
      → Arguments Γ [] parameters parameter-tele
      → Arguments Γ (reverse parameters) fields field-tele
      → FinalTerms parameters → FinalTerms fields
      → P.Coherent Φ Γ (F.advance fields (F.advance parameters F.identity))
    result-frame {p = p} {Γ = Γ} {Π = Π} {Φ = Φ} {parameters = parameters} {fields = fields}
      {parameter-tele = parameter-tele}
      parameter-declarations field-declarations parameter-arguments field-arguments
      final-parameters final-fields =
      subst (λ σ → P.Coherent Φ Γ (F.advance fields σ))
        (sym (funext (F.advance-reverse parameters F.identity)))
        (proj₂ (instantiate field-declarations parameter-size field-arguments final-fields parameter-frame))
      where
        parameters-instantiated = instantiate parameter-declarations refl
          parameter-arguments final-parameters (λ ())
        parameter-size : length (reverse parameters) ≡ p
        parameter-size = trans (length-reverse parameters)
          (trans (D.checked-length (proj₁ parameters-instantiated))
            (trans (sym (+-identityʳ (length parameter-tele)))
              (declared-length parameter-declarations)))
        parameter-frame : P.Coherent Π Γ (F.prefix (reverse parameters) F.identity)
        parameter-frame = subst (P.Coherent Π Γ)
          (funext (F.advance-reverse parameters F.identity))
          (proj₂ parameters-instantiated)

    instantiate-result⇒ : ∀ {n p f} {Γ : Ctx n} {Π : Ctx p} {Φ : Ctx f}
      {parameters fields parameter-tele field-tele t T}
      → Declared ⟨⟩ parameter-tele Π → Declared Π field-tele Φ
      → Arguments Γ [] parameters parameter-tele
      → Arguments Γ (reverse parameters) fields field-tele
      → FinalTerms parameters → FinalTerms fields
      → Φ ⊢ t ⇒ T
      → Γ ⊢ F.instantiateResult parameters fields t
          ⇒ F.instantiateResult parameters fields T
    instantiate-result⇒ pd fd pa fa fp ff der =
      P.subst⇒ (result-frame pd fd pa fa fp ff) der

    instantiate-result⇐ : ∀ {n p f} {Γ : Ctx n} {Π : Ctx p} {Φ : Ctx f}
      {parameters fields parameter-tele field-tele t T}
      → Declared ⟨⟩ parameter-tele Π → Declared Π field-tele Φ
      → Arguments Γ [] parameters parameter-tele
      → Arguments Γ (reverse parameters) fields field-tele
      → FinalTerms parameters → FinalTerms fields
      → Φ ⊢ t ⇐ T
      → Γ ⊢ F.instantiateResult parameters fields t
          ⇐ F.instantiateResult parameters fields T
    instantiate-result⇐ pd fd pa fa fp ff der =
      P.subst⇐ (result-frame pd fd pa fa fp ff) der
