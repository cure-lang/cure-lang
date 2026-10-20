------------------------------------------------------------------------
-- Native coherent substitutions and context renamings. Every typing
-- premise and conclusion uses Core.DependentTyping in ONE environment.
-- This constructs the substitution inputs; it does NOT yet transport
-- arbitrary native derivations or prove preservation.
------------------------------------------------------------------------
module Proof.DependentCoherence where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using ([]; _∷_; _++_; length; reverse)
open import Data.List.Properties using (length-++; length-reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing
  using (Ctx; ⟨⟩; extend; lookup; lookup-extend; lookup-renameCtx; Conversion)
open import Core.DependentTyping using (Opened; op[]; op∷)
import Core.DependentTyping as Native
import Core.LocalFrame as F
open import Core.Verification using (ScopedTele; tele[]; tele∷)
open import Proof.LocalFrame using (push-undoes-wk)
open import Proof.Substitution using (substS-idSub; subst-compose; substCompose; subst-rename)
open import Proof.Progress using (Final; FinalTerms; ft[]; ft∷)
import Proof.DependentNaturality as Naturality

prefix-agrees : ∀ locals T
  → substS (F.prefix locals F.identity) T ≡ F.instantiatePrefix locals T
prefix-agrees locals T = cong (λ σ → substS σ T) (funext (F.prefix-args 0 locals))

push-compose : ∀ arg τ σ locals
  → (∀ i → substCompose τ σ i ≡ F.prefix locals F.identity i)
  → ∀ i → substCompose (F.push arg τ) (extSub σ) i ≡ F.prefix (arg ∷ locals) F.identity i
push-compose arg τ σ locals equal zero = refl
push-compose arg τ σ locals equal (suc i) =
  trans (push-undoes-wk arg τ (σ i)) (equal i)

subst-renaming : ∀ ρ T → substS (λ i → tm-var (ρ i)) T ≡ rename ρ T
subst-renaming ρ T = trans (sym (subst-rename F.identity ρ T)) (substS-idSub (rename ρ T))

module NativeFrames (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv

  Coherent : ∀ {n m} → Ctx n → Ctx m → Sub → Set
  Coherent {n} Γ Δ σ = ∀ (i : Fin n) → Δ ⊢ σ (toℕ i) ⇒ substS σ (lookup Γ i)

  record Renaming {n m} (Γ : Ctx n) (Δ : Ctx m) (ρ : Ren) : Set where
    field
      index : Fin n → Fin m
      agrees : ∀ i → toℕ (index i) ≡ ρ (toℕ i)
      types : ∀ i → lookup Δ (index i) ≡ rename ρ (lookup Γ i)
  open Renaming public

  extend-index : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  extend-index idx zero = zero
  extend-index idx (suc i) = suc (idx i)

  abstract
    -- Finality is necessary only for checking-only holes. No evaluation
    -- or native preservation theorem is consumed by this induction.
    check-infer : ∀ {n} {Γ : Ctx n} {t T} → Final t → Γ ⊢ t ⇐ T → Γ ⊢ t ⇒ T
    check-infer final (⇐-lam kind checked) = ⇒-lam kind checked
    check-infer () ⇐-hole
    check-infer final (⇐-infer der equal) = ⇒-conv der equal
    check-infer final (⇐-conv checked equal) = ⇒-conv (check-infer final checked) equal
    check-infer final (⇐-cumul der le) = ⇒-cumul der le

    identity : ∀ {n} (Γ : Ctx n) → Coherent Γ Γ F.identity
    identity Γ i = subst (λ T → Γ ⊢ tm-var (toℕ i) ⇒ T)
      (sym (substS-idSub (lookup Γ i))) (⇒-var i)

    push-coherent : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ T arg}
      → Coherent Δ Γ σ → Γ ⊢ arg ⇒ substS σ T
      → Coherent (extend Δ T) Γ (F.push arg σ)
    push-coherent {σ = σ} {T = T} {arg = arg} coh checked zero =
      subst (λ A → _ ⊢ arg ⇒ A) (sym (push-undoes-wk arg σ T)) checked
    push-coherent {Δ = Δ} {σ = σ} {T = T} {arg = arg} coh checked (suc i) =
      subst (λ A → _ ⊢ σ (toℕ i) ⇒ A)
        (sym (trans (cong (substS (F.push arg σ)) (lookup-extend Δ T i))
          (push-undoes-wk arg σ (lookup Δ i)))) (coh i)

    weakening : ∀ {n} (Γ : Ctx n) T → Renaming Γ (extend Γ T) wk
    weakening Γ T = record { index = suc ; agrees = λ i → refl ; types = lookup-extend Γ T }

    extend-renaming : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ}
      → Renaming Γ Δ ρ → ∀ T → Renaming (extend Γ T) (extend Δ (rename ρ T)) (ext ρ)
    extend-renaming {Γ = Γ} {Δ = Δ} {ρ = ρ} ren T = record
      { index = extend-index (index ren)
      ; agrees = λ { zero → refl ; (suc i) → cong suc (agrees ren i) }
      ; types = λ
          { zero → ext-wk-rename ρ T
          ; (suc i) → trans (lookup-extend Δ (rename ρ T) (index ren i))
              (trans (cong (rename wk) (types ren i))
                (trans (ext-wk-rename ρ (lookup Γ i))
                  (cong (rename (ext ρ)) (sym (lookup-renameCtx wk Γ i))))) } }

    renaming-coherent : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ}
      → Renaming Γ Δ ρ → Coherent Γ Δ (λ i → tm-var (ρ i))
    renaming-coherent {Γ = Γ} {Δ = Δ} {ρ = ρ} ren i =
      subst (λ k → Δ ⊢ tm-var k ⇒ substS (λ j → tm-var (ρ j)) (lookup Γ i)) (agrees ren i)
        (subst (λ T → Δ ⊢ tm-var (toℕ (index ren i)) ⇒ T)
          (trans (types ren i) (sym (subst-renaming ρ (lookup Γ i)))) (⇒-var (index ren i)))

    declared-length : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
      → Declared Γ tele Δ → length tele + n ≡ m
    declared-length dt[] = refl
    declared-length {n = n} (dt∷ {tele = tele} scope kind rest) =
      trans (sym (+-suc (length tele) n)) (declared-length rest)

    declared-scoping : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
      → Declared Γ tele Δ → ScopedTele n tele
    declared-scoping dt[] = tele[]
    declared-scoping (dt∷ scope kind rest) = tele∷ scope (declared-scoping rest)

    -- Complete native declaration frames, including checking-only lambdas.
    -- The finality premise rejects holes rather than pretending that all
    -- checked arguments can infer their expected type.
    instantiate-coherent : ∀ {n d e} {Γ : Ctx n} {Δ : Ctx d} {Ε : Ctx e}
      {locals args tele}
      → Declared Δ tele Ε → Spine Γ locals args tele → FinalTerms args
      → Coherent Δ Γ (F.prefix locals F.identity)
      → Coherent Ε Γ (F.advance args (F.prefix locals F.identity))
    instantiate-coherent dt[] sp[] ft[] coh = coh
    instantiate-coherent {Γ = Γ} {locals = locals}
      (dt∷ {T = T} scope kind rest) (sp∷ {arg = arg} checked args) (ft∷ final finals) coh =
      instantiate-coherent rest args finals
        (push-coherent coh
          (subst (λ A → Γ ⊢ arg ⇒ A) (sym (prefix-agrees locals T)) (check-infer final checked)))

    result-frame : ∀ {n p f} {Γ : Ctx n} {Π : Ctx p} {Φ : Ctx f}
      {ps args ptele ftele}
      → Declared ⟨⟩ ptele Π → Declared Π ftele Φ
      → Spine Γ [] ps ptele → Spine Γ (reverse ps) args ftele
      → FinalTerms ps → FinalTerms args
      → Coherent Φ Γ (F.advance args (F.advance ps F.identity))
    result-frame {Γ = Γ} {Π = Π} {Φ = Φ} {ps = ps} {args = args}
      pd fd pa fa fp ff =
      subst (λ σ → Coherent Φ Γ (F.advance args σ))
        (sym (funext (F.advance-reverse ps F.identity)))
        (instantiate-coherent fd fa ff
          (subst (Coherent Π Γ) (funext (F.advance-reverse ps F.identity))
            (instantiate-coherent pd pa fp (λ ()))))

    registered-frame : ∀ {n} {Γ : Ctx n} {name family ctor ps args}
      → (valid : SignatureValid)
      → (found : findCtor name (IndEnv.families ind) ≡ just (family , ctor))
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) args (ctor-args ctor)
      → FinalTerms ps → FinalTerms args
      → Coherent (ConstructorDeclaration.field-context
          (SignatureValid.constructor-declared valid found)) Γ
          (F.advance args (F.advance ps F.identity))
    registered-frame valid found pa fa fp ff = result-frame
      (ConstructorDeclaration.parameters (SignatureValid.constructor-declared valid found))
      (ConstructorDeclaration.fields (SignatureValid.constructor-declared valid found)) pa fa fp ff

    -- General closing with an unrelated ambient caller, not just a closed
    -- declaration body. This supplies a native coherent substitution,
    -- NOT a theorem that arbitrary bodies transport along that substitution.
    close-coherent : ∀ {n d m} {Γ : Ctx n} {Δ : Ctx d} {Θ : Ctx m}
      {σ τ locals args tele}
      → Opened Δ σ tele Θ → Spine Γ locals args tele → FinalTerms args
      → Coherent Δ Γ τ
      → (∀ i → substCompose τ σ i ≡ F.prefix locals F.identity i)
      → Coherent Θ Γ (F.advance args τ)
    close-coherent op[] sp[] ft[] coh equal = coh
    close-coherent {Γ = Γ} {σ = σ} {τ = τ} {locals = locals}
      (op∷ {T = T} rest) (sp∷ {arg = arg} checked args) (ft∷ final finals) coh equal =
      close-coherent rest args finals
        (push-coherent coh
          (subst (λ A → Γ ⊢ arg ⇒ A) (sym expected) (check-infer final checked)))
        (push-compose arg τ σ locals equal)
      where
        expected : substS τ (substS σ T) ≡ F.instantiatePrefix locals T
        expected = trans (subst-compose τ σ T)
          (trans (cong (λ ρ → substS ρ T) (funext equal)) (prefix-agrees locals T))

    branch-frame : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {ps args tele}
      → Opened Γ (F.advance ps F.identity) tele Θ
      → Spine Γ (reverse ps) args tele → FinalTerms args
      → Coherent Θ Γ (F.advance args F.identity)
    branch-frame {Γ = Γ} {ps = ps} opening args finals =
      close-coherent opening args finals (identity Γ)
        (λ i → trans (substS-idSub (F.advance ps F.identity i)) (F.advance-reverse ps F.identity i))

    frame-size : ∀ {n p f} {Γ : Ctx n} {Π : Ctx p} {Φ : Ctx f}
      {ps args ptele ftele}
      → Declared ⟨⟩ ptele Π → Declared Π ftele Φ
      → Spine Γ [] ps ptele → Spine Γ (reverse ps) args ftele
      → length (reverse args ++ reverse ps) ≡ f
    frame-size {ps = ps} {args = args} {ptele = ptele} pd fd pa fa =
      trans (length-++ (reverse args))
        (trans (cong₂ _+_ (length-reverse args) (length-reverse ps))
          (trans (cong₂ _+_ (spine-length fa)
            (trans (spine-length pa) (trans (sym (+-identityʳ (length ptele))) (declared-length pd))))
            (declared-length fd)))

    registered-result-scoping : ∀ {n} {Γ : Ctx n} {name family ctor ps args}
      → (valid : SignatureValid)
      → (found : findCtor name (IndEnv.families ind) ≡ just (family , ctor))
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) args (ctor-args ctor)
      → ScopedTerms (length (reverse args ++ reverse ps)) (ctor-indices ctor)
    registered-result-scoping {family = family} {ctor = ctor} {ps = ps} {args = args} valid found pa fa =
      subst (λ d → ScopedTerms d (ctor-indices ctor))
        (sym (frame-size (ConstructorDeclaration.parameters declaration)
          (ConstructorDeclaration.fields declaration) pa fa))
        (proj₂ (ConstructorDeclaration.result-scoping declaration))
      where
        declaration : ConstructorDeclaration family ctor
        declaration = SignatureValid.constructor-declared valid found

    registered-results-rename : ∀ {n} {Γ : Ctx n} {name family ctor ps args}
      → (valid : SignatureValid)
      → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) args (ctor-args ctor)
      → ∀ ρ → renameTerms ρ (F.instantiateResults ps args (ctor-indices ctor))
        ≡ F.instantiateResults (renameTerms ρ ps) (renameTerms ρ args) (ctor-indices ctor)
    registered-results-rename {ctor = ctor} {ps = ps} {args = args} valid found pa fa ρ =
      Naturality.rename-results ρ ps args (ctor-indices ctor)
        (registered-result-scoping valid found pa fa)

    registered-results-subst : ∀ {n} {Γ : Ctx n} {name family ctor ps args}
      → (valid : SignatureValid)
      → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) args (ctor-args ctor)
      → ∀ σ → substTermsS σ (F.instantiateResults ps args (ctor-indices ctor))
        ≡ F.instantiateResults (substTermsS σ ps) (substTermsS σ args) (ctor-indices ctor)
    registered-results-subst {ctor = ctor} {ps = ps} {args = args} valid found pa fa σ =
      Naturality.subst-results σ ps args (ctor-indices ctor)
        (registered-result-scoping valid found pa fa)
