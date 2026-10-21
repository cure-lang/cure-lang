------------------------------------------------------------------------
-- Local dependent constructor declaration evidence and result transport.
-- This is NOT registration in the active closed-entry typing calculus.
------------------------------------------------------------------------
module Proof.DependentResult where

open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; []; length; reverse)
open import Data.List.Properties using (length-reverse; reverse-involutive)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Core.Syntax
open import Core.Signature
  using (IndEnv; Family; Ctor; Telescope; fam-name; fam-level; fam-params; fam-indices;
         ctor-args; ctor-params; ctor-indices; findFamily)
open import Core.Reduction using (Signature; argsSub)
open import Core.Typing
  using (Ctx; Conversion; ⟨⟩; branch-field-vars; surface-field-vars; _∈Tele_)
open import Core.Universe using (Level; _≤ˡ_)
import Core.LocalFrame as F
open import Proof.Substitution using (subst-rename-terms; substTerms-reverse)
open import Proof.Progress using (BuiltinCtors; Certified; FinalTerms)
open import Proof.Preservation using (ClosedFragmentSig; ReduceConv; CertifiedTyped)
import Proof.DependentInstantiation as Instantiation

-- Uniform result parameters are the fresh parameter variables in SURFACE
-- order, shifted past the constructor fields; not arbitrary expressions.
parameter-slots : ℕ → ℕ → List Term
parameter-slots fields parameters =
  renameTerms (λ i → fields + i) (surface-field-vars parameters)

UniformParameters : Family → Ctor → Set
UniformParameters family ctor =
  ctor-params ctor ≡ parameter-slots (length (ctor-args ctor)) (length (fam-params family))

module Results (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.Typing.Typing ind sig conv
  module T = Instantiation.Telescopes ind sig conv
  module D = T.D

  -- The levels belong to the ACTUAL declaration kind witnesses, not an
  -- unchecked positivity/universe-ok boolean on a raw family record.
  LevelsBelow : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
    → Level → T.Declared Γ tele Δ → Set
  LevelsBelow cap T.dt[] = ⊤
  LevelsBelow cap (T.dt∷ {l = l} scoped kind rest) = l ≤ˡ cap × LevelsBelow cap rest

  record ResultSpines {n} (Γ : Ctx n) (family : Family)
    (parameters indices : List Term) : Set where
    field
      parameters-checked : D.Checked Γ [] parameters (fam-params family)
      indices-checked : D.Checked Γ (reverse parameters) indices (fam-indices family)
  open ResultSpines public

  result-arities : ∀ {n} {Γ : Ctx n} {family ps is}
    → ResultSpines Γ family ps is
    → length ps ≡ length (fam-params family) × length is ≡ length (fam-indices family)
  result-arities checked =
    D.checked-length (parameters-checked checked) , D.checked-length (indices-checked checked)

  -- All LOCAL evidence needed here is tied to the same family/ctor.
  -- Global lookup, recursive signature validity, positivity and migration
  -- of the active constructor/branch rules remain separate obligations.
  record LocalDeclaration (family : Family) (ctor : Ctor)
    {p i f} (Π : Ctx p) (Ι : Ctx i) (Φ : Ctx f) : Set where
    field
      parameter-declarations : T.Declared ⟨⟩ (fam-params family) Π
      index-declarations : T.Declared Π (fam-indices family) Ι
      field-declarations : T.Declared Π (ctor-args ctor) Φ
      field-levels : LevelsBelow (fam-level family) field-declarations
      result-scoping : ScopedTerms f (ctor-params ctor) × ScopedTerms f (ctor-indices ctor)
      uniform-parameters : UniformParameters family ctor
      result-spines : ResultSpines Φ family (ctor-params ctor) (ctor-indices ctor)
  open LocalDeclaration public

  module Transport (closed : ClosedFragmentSig ind sig) (rc : ReduceConv sig conv)
    (typed : CertifiedTyped ind sig conv) (bc : BuiltinCtors ind) (cert : Certified sig) where
    module I = T.Instantiation closed rc typed bc cert
    module P = I.P
    module S = D.Stability closed rc typed bc cert

    subst-result-spines : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {family ps is σ}
      → P.Coherent Γ Δ σ → ResultSpines Γ family ps is
      → ResultSpines Δ family (substTermsS σ ps) (substTermsS σ is)
    subst-result-spines {Δ = Δ} {family = family} {ps = ps} {is = is} {σ = σ} coh checked = record
      { parameters-checked = S.subst-checked coh (parameters-checked checked)
      ; indices-checked = subst (λ locals → D.Checked Δ locals (substTermsS σ is) (fam-indices family))
          (substTerms-reverse σ ps) (S.subst-checked coh (indices-checked checked)) }

    -- Pure slot projection used below. Reversing checked values is NOT
    -- appropriate for the caller's ambient context or declaration syntax.
    project-parameters : ∀ tele parameters fields
      → length parameters ≡ length tele
      → F.instantiateResults parameters fields (parameter-slots (length fields) (length tele))
          ≡ parameters
    project-parameters tele parameters fields size =
      trans (sym (substTerms-map σ (parameter-slots (length fields) (length tele))))
        (trans (subst-rename-terms σ (λ i → length fields + i) vars)
          (trans (cong (λ τ → substTermsS τ vars)
            (funext (F.advance-base fields (F.advance parameters F.identity))))
            (trans (cong (λ τ → substTermsS τ vars)
              (funext (λ i → trans (F.advance-reverse parameters F.identity i)
                (F.prefix-args 0 (reverse parameters) i))))
              (trans (substTerms-reverse (argsSub (reverse parameters)) (branch-field-vars (length tele)))
                (trans (cong reverse
                  (P.substArgs-field-vars {args = reverse parameters} tele
                    (trans (length-reverse parameters) size)))
                  (reverse-involutive parameters))))))
      where
        σ = F.advance fields (F.advance parameters F.identity)
        vars = surface-field-vars (length tele)

    uniform-instantiates : ∀ family ctor parameters fields
      → UniformParameters family ctor
      → length parameters ≡ length (fam-params family)
      → length fields ≡ length (ctor-args ctor)
      → F.instantiateResults parameters fields (ctor-params ctor) ≡ parameters
    uniform-instantiates family ctor parameters fields uniform parameter-size field-size =
      trans (cong (F.instantiateResults parameters fields) uniform)
        (trans (cong (λ k → F.instantiateResults parameters fields
          (parameter-slots k (length (fam-params family)))) (sym field-size))
          (project-parameters (fam-params family) parameters fields parameter-size))

    instantiate-results : ∀ {n p i f} {Γ : Ctx n} {Π : Ctx p} {Ι : Ctx i} {Φ : Ctx f}
      {family ctor parameters fields}
      → LocalDeclaration family ctor Π Ι Φ
      → T.Arguments Γ [] parameters (fam-params family)
      → T.Arguments Γ (reverse parameters) fields (ctor-args ctor)
      → FinalTerms parameters → FinalTerms fields
      → ResultSpines Γ family parameters (F.instantiateResults parameters fields (ctor-indices ctor))
    instantiate-results {Γ = Γ} {family = family} {ctor = ctor}
      {parameters = parameters} {fields = fields} declaration pa fa fp ff =
      subst (λ ps → ResultSpines Γ family ps indices)
        (uniform-instantiates family ctor parameters fields (uniform-parameters declaration)
          (T.arguments-length pa) (T.arguments-length fa))
        (subst₂ (ResultSpines Γ family)
          (substTerms-map σ (ctor-params ctor)) (substTerms-map σ (ctor-indices ctor))
          (subst-result-spines
            (I.result-frame (parameter-declarations declaration) (field-declarations declaration) pa fa fp ff)
            (result-spines declaration)))
      where
        σ = F.advance fields (F.advance parameters F.identity)
        indices = F.instantiateResults parameters fields (ctor-indices ctor)

    -- A real adapter to existing data formation, ONLY where its old
    -- flat telescopes are sound: all entries must be individually closed.
    active-result-kind : ∀ {n} {Γ : Ctx n} {name family ps is}
      → findFamily name (IndEnv.families ind) ≡ just family
      → (∀ {A} → A ∈Tele fam-params family → Scoped 0 A)
      → (∀ {A} → A ∈Tele fam-indices family → Scoped 0 A)
      → ResultSpines Γ family ps is
      → Γ ⊢ tm-data name ps is ⇒ tm-type (fam-level family)
    active-result-kind found cp ci checked =
      ⇒-data found (D.closed-to-flat cp (parameters-checked checked))
        (D.closed-to-flat ci (indices-checked checked))
