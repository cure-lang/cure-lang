------------------------------------------------------------------------
-- A BOUNDED base-checked registry layer, not the full Core typing calculus.
-- Declaration types and caller arguments are checked in `base`. Actual
-- registry lookups carry local dependent declaration evidence. The two
-- environments are deliberately NOT conflated: registry entries may be
-- open locally, whereas the existing substitution theorem requires a
-- closed-entry BASE signature. Recursive extension checking, elimination
-- and full dependent preservation/refinement remain separate obligations.
------------------------------------------------------------------------
module Proof.DependentRegistry where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax
open import Core.Signature
  using (IndEnv; Family; Ctor; fam-name; ctor-name; fam-params; fam-indices;
         ctor-args; ctor-indices; findFamily; findCtor)
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion; ⟨⟩)
import Core.LocalFrame as F
open import Proof.Progress using (FinalTerms; BuiltinCtors; Certified)
open import Proof.Preservation using (ClosedFragmentSig; ReduceConv; CertifiedTyped)
import Proof.DependentResult as Result

module Layer (base : IndEnv) (sig : Signature) (conv : Conversion) (registry : IndEnv) where
  module R = Result.Results base sig conv
  module T = R.T

  record FamilyDeclaration (family : Family) : Set where
    field
      {p i} : ℕ
      parameter-context : Ctx p
      index-context : Ctx i
      parameters : T.Declared ⟨⟩ (fam-params family) parameter-context
      indices : T.Declared parameter-context (fam-indices family) index-context

  record ConstructorDeclaration (family : Family) (ctor : Ctor) : Set where
    field
      {p i f} : ℕ
      parameter-context : Ctx p
      index-context : Ctx i
      field-context : Ctx f
      local-declaration : R.LocalDeclaration family ctor parameter-context index-context field-context

  -- Quantification is restricted to ACTUAL lookups, not arbitrary raw
  -- records. Owner visibility prevents duplicate family names from making
  -- constructor result formation refer to a different family record.
  -- Freshness prevents this separate layer from shadowing BASE identities.
  record Registry : Set where
    field
      family-declared : ∀ {name family}
        → findFamily name (IndEnv.families registry) ≡ just family
        → FamilyDeclaration family
      constructor-declared : ∀ {name family ctor}
        → findCtor name (IndEnv.families registry) ≡ just (family , ctor)
        → ConstructorDeclaration family ctor
      owner-visible : ∀ {name family ctor}
        → findCtor name (IndEnv.families registry) ≡ just (family , ctor)
        → findFamily (fam-name family) (IndEnv.families registry) ≡ just family
      family-fresh : ∀ {name family}
        → findFamily name (IndEnv.families registry) ≡ just family
        → findFamily (fam-name family) (IndEnv.families base) ≡ nothing
      constructor-fresh : ∀ {name family ctor}
        → findCtor name (IndEnv.families registry) ≡ just (family , ctor)
        → findCtor (ctor-name ctor) (IndEnv.families base) ≡ nothing
  open Registry public

  -- These records are the explicitly bounded admission judgments, NOT
  -- Core.Typing._⊢_⇒_. Their validity includes the checked whole registry.
  record Formation {n} (Γ : Ctx n) (name : Name) (ps is : List Term) : Set where
    field
      registry-valid : Registry
      family : Family
      found : findFamily name (IndEnv.families registry) ≡ just family
      spines : R.ResultSpines Γ family ps is
  open Formation public

  record Application {n} (Γ : Ctx n) (name : Name) (ps args : List Term) : Set where
    field
      registry-valid : Registry
      family : Family
      ctor : Ctor
      found : findCtor name (IndEnv.families registry) ≡ just (family , ctor)
      parameters : T.Arguments Γ [] ps (fam-params family)
      fields : T.Arguments Γ (reverse ps) args (ctor-args ctor)
      parameters-final : FinalTerms ps
      fields-final : FinalTerms args

  module Admission (closed : ClosedFragmentSig base sig) (rc : ReduceConv sig conv)
    (typed : CertifiedTyped base sig conv) (bc : BuiltinCtors base) (cert : Certified sig) where
    module K = R.Transport closed rc typed bc cert
    module P = K.P

    result-formation : ∀ {n} {Γ : Ctx n} {name ps args}
      → (app : Application Γ name ps args)
      → Formation Γ (fam-name (Application.family app)) ps
          (F.instantiateResults ps args (ctor-indices (Application.ctor app)))
    result-formation app = record
      { registry-valid = Application.registry-valid app
      ; family = Application.family app
      ; found = owner-visible (Application.registry-valid app) (Application.found app)
      ; spines = K.instantiate-results
          (ConstructorDeclaration.local-declaration
            (constructor-declared (Application.registry-valid app) (Application.found app)))
          (Application.parameters app) (Application.fields app)
          (Application.parameters-final app) (Application.fields-final app) }

    -- Substitution acts on the checked BASE caller. It does not assume
    -- closed registry entries or a new dependent-preservation oracle.
    subst-formation : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {name ps is σ}
      → P.Coherent Γ Δ σ → Formation Γ name ps is
      → Formation Δ name (substTermsS σ ps) (substTermsS σ is)
    subst-formation coh admitted = record
      { registry-valid = registry-valid admitted
      ; family = family admitted
      ; found = found admitted
      ; spines = K.subst-result-spines coh (spines admitted) }
