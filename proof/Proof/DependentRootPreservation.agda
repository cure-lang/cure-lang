------------------------------------------------------------------------
-- Native beta/zeta/delta root contractions, at one fixed checking goal.
-- These consume the proved supported substitution/weakening fragment.
-- No legacy preservation, base registry, or executable totality claim.
-- Congruence and arbitrary native derivation inversion remain separate.
------------------------------------------------------------------------
module Proof.DependentRootPreservation where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature using (IndEnv)
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Reduction
import Core.DependentTyping as Native
import Proof.DependentTransport as Transport
open import Proof.Progress using (Final)
open import Proof.Substitution using (rename-closed)

module Roots (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  module T = Transport.Transport ind sig conv
  open Conversion conv

  Preserved : ∀ {n} → Ctx n → Term → Term → Term → Set
  Preserved Γ source target goal =
    (Γ ⊢ source ⇐ goal) × _⇝_ sig source target × T.Check Γ target goal

  module Valid (valid : SignatureValid) where
    module V = T.Valid valid

    beta-at : ∀ {n} {Γ : Ctx n} {g d b a c l goal}
      → Γ ⊢ d ⇒ tm-type l
      → (body : extend Γ d ⊢ b ⇐ c) → T.Supported⇐ body
      → T.Infer Γ a d
      → substTopT a c ≈ goal
      → Preserved Γ (tm-app (tm-lam g d b) a) (substTopT a b) goal
    beta-at kind body gb arg equal
      with V.subst⇐ (V.top-coherent arg) body gb
    ... | checked , good = ⇐-infer (⇒-app (⇒-lam kind body) (proj₁ arg)) equal ,
      β , (⇐-conv checked equal , good)

    zeta-at : ∀ {n} {Γ : Ctx n} {g ty v b l T′ goal}
      → Γ ⊢ ty ⇒ tm-type l
      → (value : Γ ⊢ v ⇐ ty) → T.Supported⇐ value → Final v
      → (body : extend Γ ty ⊢ b ⇒ T′) → T.Supported⇒ body
      → substTopT v T′ ≈ goal
      → Preserved Γ (tm-let g ty v b) (substTopT v b) goal
    zeta-at kind value gv final body gb equal
      with V.subst⇒ (V.top-coherent (V.check-infer final value gv)) body gb
    ... | typed , good = ⇐-infer (⇒-let kind value body) equal ,
      ζ , (⇐-infer typed equal , good)

    -- Closed native derivations weaken into any caller using only the
    -- proved fragment theorem, not the legacy closed-entry judgment.
    weaken-closed : ∀ {n} {Γ : Ctx n} {t T′}
      → Scoped 0 t → Scoped 0 T′
      → (typed : ⟨⟩ ⊢ t ⇒ T′) → T.Supported⇒ typed → T.Infer Γ t T′
    weaken-closed {Γ = Γ} scoped type-scoped typed good =
      T.cast⇒ (rename-closed scoped) (rename-closed type-scoped)
        (V.rename⇒ {ρ = λ i → i}
          (record { index = λ () ; agrees = λ () ; types = λ () }) typed good)

    BodyType : ∀ {name b} → Signature.body sig name ≡ just b → Term
    BodyType found = proj₁ (SignatureValid.global-body valid found)

    BodySupport : ∀ {name b} → Signature.body sig name ≡ just b → Set
    BodySupport found =
      T.Supported⇒ (proj₂ (proj₂ (proj₂ (SignatureValid.global-body valid found))))

    delta-at : ∀ {n} {Γ : Ctx n} {name b goal}
      → (found : Signature.body sig name ≡ just b)
      → BodySupport found → BodyType found ≈ goal
      → Preserved Γ (tm-global name) b goal
    delta-at found supported equal =
      ⇐-infer (⇒-global declared) equal , δ found ,
      (⇐-infer (proj₁ weakened) equal , proj₂ weakened)
      where
        declaration = SignatureValid.global-body valid found
        declared = proj₁ (proj₂ declaration)
        weakened = weaken-closed (proj₁ (proj₂ (proj₂ declaration)))
          (proj₁ (SignatureValid.global-type valid declared))
          (proj₂ (proj₂ (proj₂ declaration))) supported
