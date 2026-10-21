------------------------------------------------------------------------
-- Every native typing derivation scopes its TERM, including nested cases.
-- No claim that arbitrary conversion intermediates scope their TYPES.
-- Signature validity and the legacy closed-entry fragment are not needed.
------------------------------------------------------------------------
module Proof.DependentScoping where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using ([]; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv)
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion)
import Core.DependentTyping as Native

opened-length : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ tele}
  → Native.Opened Γ σ tele Δ → n + length tele ≡ m
opened-length {n = n} Native.op[] = +-identityʳ n
opened-length {n = n} (Native.op∷ {tele = tele} rest) =
  trans (+-suc n (length tele)) (opened-length rest)

module Scoping (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv

  mutual
    infer-scoped : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Scoped n t
    infer-scoped (⇒-type level) = sc-type
    infer-scoped (⇒-var i) = sc-var (toℕ<n i)
    infer-scoped (⇒-pi d c) = sc-pi (infer-scoped d) (infer-scoped c)
    infer-scoped (⇒-lam d b) = sc-lam (infer-scoped d) (check-scoped b)
    infer-scoped (⇒-app f a) = sc-app (infer-scoped f) (infer-scoped a)
    infer-scoped (⇒-let ty v b) = sc-let (infer-scoped ty) (check-scoped v) (infer-scoped b)
    infer-scoped (⇒-global found) = sc-global
    infer-scoped ⇒-int_type = sc-int_type
    infer-scoped ⇒-float_type = sc-float_type
    infer-scoped ⇒-binary_type = sc-binary_type
    infer-scoped ⇒-atom_type = sc-atom_type
    infer-scoped ⇒-int_lit = sc-int_lit
    infer-scoped ⇒-float_lit = sc-float_lit
    infer-scoped ⇒-atom_lit = sc-atom_lit
    infer-scoped (⇒-nat_lit builtin found ps is) = sc-nat_lit
    infer-scoped (⇒-bounded_lit builtin found ps is) = sc-bounded_lit
    infer-scoped (⇒-data found ps is) = sc-data (spine-scoped ps) (spine-scoped is)
    infer-scoped (⇒-ctor found ps fields) = sc-ctor (spine-scoped fields)
    infer-scoped (⇒-case wf found s ps is (motive scoped kind typed) branches covered) =
      sc-case (infer-scoped s) scoped (branches-scoped branches)
    infer-scoped (⇒-effect_type t) = sc-effect_type (infer-scoped t)
    infer-scoped (⇒-effect_pure t) = sc-effect_pure (infer-scoped t)
    infer-scoped (⇒-effect_bind e k) = sc-effect_bind (infer-scoped e) (infer-scoped k)
    infer-scoped (⇒-conv t equal) = infer-scoped t
    infer-scoped (⇒-cumul t le) = infer-scoped t

    check-scoped : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇐ T → Scoped n t
    check-scoped (⇐-lam d b) = sc-lam (infer-scoped d) (check-scoped b)
    check-scoped ⇐-hole = sc-hole
    check-scoped (⇐-infer t equal) = infer-scoped t
    check-scoped (⇐-conv t equal) = check-scoped t
    check-scoped (⇐-cumul t le) = infer-scoped t

    spine-scoped : ∀ {n} {Γ : Ctx n} {locals args tele}
      → Spine Γ locals args tele → ScopedTerms n args
    spine-scoped sp[] = st[]
    spine-scoped (sp∷ arg rest) = st∷ (check-scoped arg) (spine-scoped rest)

    branches-scoped : ∀ {n} {Γ : Ctx n} {family ps mot brs}
      → Branches Γ family ps mot brs → ScopedBranches n brs
    branches-scoped br[] = sb[]
    branches-scoped (br∷ {b = b} found owner opening wf checked rest) =
      sb∷ (sbranch (subst (λ n → Scoped n b) (sym (opened-length opening))
        (check-scoped checked))) (branches-scoped rest)
