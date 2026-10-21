------------------------------------------------------------------------
-- Native whole-case iota preservation through arbitrary scrutinee type
-- conversions. Selected bodies/images may contain arbitrary nested cases.
-- Data components are supplied by a separately PROVED conversion model.
------------------------------------------------------------------------
module Proof.DependentGeneralIota where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Core.Syntax
open import Core.Signature
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; Conversion; All2; a2[]; a2∷)
open import Core.Reduction
open import Core.Coverage using (CaseCoverage)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentGeneralTransport as General
import Proof.DependentConstructorInversion as Inversion
import Proof.DependentSpineConversion as SpineConversion
open import Proof.DependentDataConversion using (DataComponents)
open import Proof.DependentIota using (case-goal; goal-agreement)
open import Proof.Progress using (FinalTerms)

module Preservation (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (valid : Native.Typing.SignatureValid ind sig conv) (components : DataComponents conv) where
  open Native.Typing ind sig conv
  open Conversion conv
  module G = General.General ind sig conv
  module V = G.Valid valid
  module I = Inversion.Laws ind sig conv
  module IV = I.Valid valid
  module DI = I.DataGoal components
  module L = SpineConversion.Laws ind sig conv

  all2-sym : ∀ {xs ys} → All2 _≈_ xs ys → All2 _≈_ ys xs
  all2-sym a2[] = a2[]
  all2-sym (a2∷ equal rest) = a2∷ (≈-sym equal) (all2-sym rest)
  all2-trans : ∀ {xs ys zs} → All2 _≈_ xs ys → All2 _≈_ ys zs → All2 _≈_ xs zs
  all2-trans a2[] a2[] = a2[]
  all2-trans (a2∷ first rest) (a2∷ second tail) = a2∷ (≈-trans first second) (all2-trans rest tail)
  all2-append : ∀ {xs ys us vs}
    → All2 _≈_ xs ys → All2 _≈_ us vs → All2 _≈_ (xs ++ us) (ys ++ vs)
  all2-append a2[] tail = tail
  all2-append (a2∷ equal rest) tail = a2∷ equal (all2-append rest tail)
  all2-reverse : ∀ {xs ys} → All2 _≈_ xs ys → All2 _≈_ (reverse xs) (reverse ys)
  all2-reverse a2[] = a2[]
  all2-reverse (a2∷ {x = x} {y = y} {xs = xs} {ys = ys} equal rest) =
    subst₂ (All2 _≈_) (sym (unfold-reverse x xs)) (sym (unfold-reverse y ys))
      (all2-append (all2-reverse rest) (a2∷ equal a2[]))

  -- All premises of the REAL native case rule, with its scrutinee already
  -- typed through any conversion chain at the case's actual ps/is.
  record SourceCase {n} (Γ : Ctx n) (name : Name) (fields : List Term)
    (mot : Term) (brs : List Branch) : Set where
    field
      family-name : Name
      family : Family
      parameters indices : List Term
      found-family : findFamily family-name (IndEnv.families ind) ≡ just family
      caller : WellFormed Γ
      scrutinee : Γ ⊢ tm-ctor name fields ⇒ tm-data family-name parameters indices
      parameters-checked : Spine Γ [] parameters (fam-params family)
      indices-checked : Spine Γ (reverse parameters) indices (fam-indices family)
      level : Level
      motive-valid : Motive Γ family parameters mot level
      branches : Branches Γ family parameters mot brs
      coverage : CaseCoverage ind family-name brs

  original-goal : ∀ {n} {Γ : Ctx n} {name fields mot brs}
    → SourceCase Γ name fields mot brs → Term
  original-goal {name = name} {fields = fields} {mot = mot} source =
    Native.apps mot (SourceCase.indices source ++ tm-ctor name fields ∷ [])

  source-typed : ∀ {n} {Γ : Ctx n} {name fields mot brs}
    → (source : SourceCase Γ name fields mot brs)
    → Γ ⊢ tm-case (tm-ctor name fields) mot brs ⇒ original-goal source
  source-typed source = ⇒-case (SourceCase.caller source) (SourceCase.found-family source)
    (SourceCase.scrutinee source) (SourceCase.parameters-checked source) (SourceCase.indices-checked source)
    (SourceCase.motive-valid source) (SourceCase.branches source) (SourceCase.coverage source)

  selected-contract : ∀ {n} {Γ : Ctx n} {family ctor name ps fields mot brs ar b}
    → WellFormed Γ
    → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
    → Spine Γ (reverse ps) fields (ctor-args ctor) → FinalTerms fields
    → Branches Γ family ps mot brs
    → findBranch name brs ≡ just (name , ar , b)
    → length (ctor-args ctor) ≡ ar
      × (Γ ⊢ substArgs fields b ⇐ case-goal name ps fields ctor mot)
  selected-contract wf found actual finals br[] ()
  selected-contract {name = name} {ps = ps} {fields = fields} {mot = mot}
    wf found actual finals
    (br∷ {name = cn} {ctor = ct} entry refl opening branch-wf body rest) selected with name ≟ cn
  ... | yes refl with just-inj (trans (sym found) entry) | just-inj selected
  ... | refl | refl = refl ,
    G.cast⇐ refl (goal-agreement name ps fields ct mot (spine-length actual))
      (V.contract-branch {ps = ps} wf opening actual finals body)
  selected-contract {name = name} wf found actual finals
    (br∷ {name = cn} entry refl opening branch-wf body rest) selected
    | no different = selected-contract wf found actual finals rest selected

  owner-matches : ∀ {n} {Γ : Ctx n} {name fields target ps is family}
    → findFamily target (IndEnv.families ind) ≡ just family
    → (view : DI.DataView Γ name fields target ps is)
    → I.ConstructorView.family (DI.DataView.native view) ≡ family
  owner-matches found view = just-inj (trans (sym owner-found) found)
    where
      native = DI.DataView.native view
      owner-found = subst (λ name → findFamily name (IndEnv.families ind) ≡ just (I.ConstructorView.family native))
        (DI.DataView.family-equal view) (IV.owner-found native)

  preserve-at : ∀ {n} {Γ : Ctx n} {name fields mot brs ar b goal}
    → (source : SourceCase Γ name fields mot brs) → FinalTerms fields
    → findBranch name brs ≡ just (name , ar , b)
    → original-goal source ≈ goal
    → (Γ ⊢ tm-case (tm-ctor name fields) mot brs ⇐ goal)
      × _⇝_ sig (tm-case (tm-ctor name fields) mot brs) (substArgs fields b)
      × (Γ ⊢ substArgs fields b ⇐ goal)
  preserve-at {name = name} {fields = fields} {mot = mot} source finals selected equal
    with DI.data-inference (SourceCase.scrutinee source)
  ... | view
    with selected-contract (SourceCase.caller source)
      (trans (I.ConstructorView.found (DI.DataView.native view))
        (cong (λ family → just (family , I.ConstructorView.ctor (DI.DataView.native view)))
          (owner-matches (SourceCase.found-family source) view)))
      (L.spine-locals (all2-reverse (DI.DataView.parameters-convertible view))
        (I.ConstructorView.fields-checked (DI.DataView.native view)))
      finals (SourceCase.branches source) selected
  ... | arity , checked = ⇐-infer (source-typed source) equal ,
    ι selected (trans (spine-length (I.ConstructorView.fields-checked (DI.DataView.native view))) arity) ,
    ⇐-conv checked (≈-trans instantiated-goal equal)
    where
      native = DI.DataView.native view
      fresh-indices = F.instantiateResults (SourceCase.parameters source) fields
        (ctor-indices (I.ConstructorView.ctor native))
      indices-convertible : All2 _≈_ fresh-indices (SourceCase.indices source)
      indices-convertible = all2-trans
        (all2-sym (L.instantiateResults-cong
          (DI.DataView.parameters-convertible view) (L.all2-refl fields)
          (ctor-indices (I.ConstructorView.ctor native))))
        (DI.DataView.indices-convertible view)
      instantiated-goal : case-goal name (SourceCase.parameters source) fields
        (I.ConstructorView.ctor native) mot ≈ original-goal source
      instantiated-goal = L.apps-cong (≈-refl {t = mot})
        (all2-append indices-convertible
          (a2∷ (≈-refl {t = tm-ctor name fields}) a2[]))
