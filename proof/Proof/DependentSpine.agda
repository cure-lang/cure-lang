------------------------------------------------------------------------
-- Checked foundation for the forthcoming telescope/branch migration.
-- This judgment instantiates each declaration using PRECEDING values and
-- requires both a kind derivation and a checking derivation. It does not
-- replace Core.Typing's constructor/data/branch rules at this checkpoint.
------------------------------------------------------------------------
module Proof.DependentSpine where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv; Telescope)
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion; lookup; _∈Tele_; ∈-here; ∈-there)
open import Core.Verification using (ScopedTele; tele[]; tele∷)
open import Core.LocalFrame using (instantiatePrefix)
open import Proof.LocalFrame using (rename-local; subst-local)
open import Proof.Substitution using (substS-closed)
open import Proof.Progress using (BuiltinCtors; Certified)
open import Proof.Preservation
  using (ClosedFragmentSig; ReduceConv; CertifiedTyped; module Preserve)

module Spines (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.Typing.Typing ind sig conv

  data Checked {n} (Γ : Ctx n) : List Term → List Term → Telescope → Set where
    ds[] : ∀ {locals} → Checked Γ locals [] []
    ds∷ : ∀ {locals arg args name T tele l}
      → Scoped (length locals) T
      → Γ ⊢ instantiatePrefix locals T ⇒ tm-type l
      → Γ ⊢ arg ⇐ instantiatePrefix locals T
      → Checked Γ (arg ∷ locals) args tele
      → Checked Γ locals (arg ∷ args) ((name , T) ∷ tele)

  checked-scoping : ∀ {n} {Γ : Ctx n} {locals args tele}
    → Checked Γ locals args tele → ScopedTele (length locals) tele
  checked-scoping ds[] = tele[]
  checked-scoping (ds∷ scoped kind arg rest) = tele∷ scoped (checked-scoping rest)

  checked-length : ∀ {n} {Γ : Ctx n} {locals args tele}
    → Checked Γ locals args tele → length args ≡ length tele
  checked-length ds[] = refl
  checked-length (ds∷ scoped kind arg rest) = cong suc (checked-length rest)

  -- A real connection to the ACTIVE closed-entry checker. For closed
  -- declarations local instantiation is identity, so no new oracle is
  -- needed to obtain the old spine judgment. The reverse implication
  -- would additionally need entry-kind evidence, which the old rule lacks.
  closed-to-flat : ∀ {n} {Γ : Ctx n} {locals args tele}
    → (∀ {T} → T ∈Tele tele → Scoped 0 T)
    → Checked Γ locals args tele → Γ ⊢* args ⇐* tele
  closed-to-flat closed ds[] = ⊢*[]
  closed-to-flat {Γ = Γ} closed (ds∷ {arg = arg} {T = T} scoped kind checked rest) =
    ⊢*∷ (subst (λ A → Γ ⊢ arg ⇐ A) (substS-closed (closed ∈-here)) checked)
      (closed-to-flat (λ entry → closed (∈-there entry)) rest)

  ren-length : ∀ ρ xs → length (renameTerms ρ xs) ≡ length xs
  ren-length ρ [] = refl
  ren-length ρ (x ∷ xs) = cong suc (ren-length ρ xs)
  sub-length : ∀ σ xs → length (substTermsS σ xs) ≡ length xs
  sub-length σ [] = refl
  sub-length σ (x ∷ xs) = cong suc (sub-length σ xs)

  module Stability (closed : ClosedFragmentSig ind sig) (rc : ReduceConv sig conv)
    (typed : CertifiedTyped ind sig conv) (bc : BuiltinCtors ind) (cert : Certified sig) where
    module P = Preserve ind sig conv closed rc typed bc cert

    rename-checked : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {locals args tele ρ}
      → (idx : Fin n → Fin m)
      → (∀ i → toℕ (idx i) ≡ ρ (toℕ i))
      → (∀ i → lookup Δ (idx i) ≡ rename ρ (lookup Γ i))
      → Checked Γ locals args tele
      → Checked Δ (renameTerms ρ locals) (renameTerms ρ args) tele
    rename-checked idx coh law ds[] = ds[]
    rename-checked {Δ = Δ} {ρ = ρ} idx coh law
      (ds∷ {locals = locals} {arg = arg} {T = T} {l = l} scoped kind checked rest) =
      ds∷ (subst (λ d → Scoped d T) (sym (ren-length ρ locals)) scoped)
        (subst (λ A → Δ ⊢ A ⇒ tm-type l)
          (rename-local {locals = locals} {ty = T} scoped ρ) (P.ren⇒ idx coh law kind))
        (subst (λ A → Δ ⊢ rename ρ arg ⇐ A)
          (rename-local {locals = locals} {ty = T} scoped ρ) (P.ren⇐ idx coh law checked))
        (rename-checked idx coh law rest)

    subst-checked : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {locals args tele σ}
      → P.Coherent Γ Δ σ → Checked Γ locals args tele
      → Checked Δ (substTermsS σ locals) (substTermsS σ args) tele
    subst-checked coh ds[] = ds[]
    subst-checked {Δ = Δ} {σ = σ} coh
      (ds∷ {locals = locals} {arg = arg} {T = T} {l = l} scoped kind checked rest) =
      ds∷ (subst (λ d → Scoped d T) (sym (sub-length σ locals)) scoped)
        (subst (λ A → Δ ⊢ A ⇒ tm-type l)
          (subst-local {locals = locals} {ty = T} scoped σ) (P.subst⇒ coh kind))
        (subst (λ A → Δ ⊢ substS σ arg ⇐ A)
          (subst-local {locals = locals} {ty = T} scoped σ) (P.subst⇐ coh checked))
        (subst-checked coh rest)
