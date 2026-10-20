------------------------------------------------------------------------
-- Ordinary constructor iota preservation for actual native source cases.
-- Exact fields-only frames; selected bodies/actual fields use the checked
-- case-free substitution fragment. No base-registry typing assumptions.
-- This is not general native preservation or executable refinement.
------------------------------------------------------------------------
module Proof.DependentIota where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; reverse; map)
open import Data.List.Properties using (length-reverse; reverse-involutive)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Universe using (Level)
open import Core.Signature
open import Core.Reduction
open import Core.Typing using (Ctx; Conversion; branch-field-vars; surface-field-vars; upto)
open import Core.Coverage using (CaseCoverage)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentTransport as Transport
open import Proof.Progress using (FinalTerms)
open import Proof.LocalFrame using (staged-contraction)
open import Proof.Substitution using (substTerms-reverse; substS-argsSub-shift)

map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) xs
  → map f (map g xs) ≡ map (λ x → f (g x)) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) = cong₂ _∷_ refl (map-compose f g xs)

prefix-values : ∀ k xs → map (argsSub-go k xs) (upto (length xs)) ≡ xs
prefix-values k [] = refl
prefix-values k (x ∷ xs) = cong₂ _∷_ refl
  (trans (map-compose (argsSub-go k (x ∷ xs)) suc (upto (length xs)))
    (prefix-values (suc k) xs))

prefix-fields : ∀ xs ar → length xs ≡ ar
  → substTermsS (argsSub xs) (branch-field-vars ar) ≡ xs
prefix-fields xs .(length xs) refl =
  trans (substTerms-map (argsSub xs) (branch-field-vars (length xs)))
    (trans (map-compose (substS (argsSub xs)) tm-var (upto (length xs)))
      (prefix-values 0 xs))

surface-fields : ∀ fields ar → length fields ≡ ar
  → substTermsS (argsSub (reverse fields)) (surface-field-vars ar) ≡ fields
surface-fields fields ar size =
  trans (substTerms-reverse (argsSub (reverse fields)) (branch-field-vars ar))
    (trans (cong reverse (prefix-fields (reverse fields) ar
      (trans (length-reverse fields) size))) (reverse-involutive fields))

subst-apps : ∀ σ function args
  → substS σ (Native.apps function args)
    ≡ Native.apps (substS σ function) (substTermsS σ args)
subst-apps σ function [] = refl
subst-apps σ function (arg ∷ args) = subst-apps σ (tm-app function arg) args

subst-append : ∀ σ xs ys
  → substTermsS σ (xs ++ ys) ≡ substTermsS σ xs ++ substTermsS σ ys
subst-append σ [] ys = refl
subst-append σ (x ∷ xs) ys = cong₂ _∷_ refl (subst-append σ xs ys)

staged-indices : ∀ ps fields ar indices → length fields ≡ ar
  → substTermsS (argsSub (reverse fields)) (map (F.specializeParameters ar ps) indices)
    ≡ F.instantiateResults ps fields indices
staged-indices ps fields ar [] size = refl
staged-indices ps fields ar (index ∷ indices) size =
  cong₂ _∷_
    (trans (cong (λ k → substArgs fields (F.specializeParameters k ps index)) (sym size))
      (staged-contraction ps fields index))
    (staged-indices ps fields ar indices size)

case-goal : Name → List Term → List Term → Ctor → Term → Term
case-goal name ps fields ctor mot =
  Native.apps mot (F.instantiateResults ps fields (ctor-indices ctor)
    ++ tm-ctor name fields ∷ [])

-- This equality is about the ACTIVE native branch goal. It does not
-- assume motive validity or a legacy preservation instance.
goal-agreement : ∀ name ps fields ctor mot
  → length fields ≡ length (ctor-args ctor)
  → substArgs fields (Native.branchGoal name ps ctor mot)
    ≡ case-goal name ps fields ctor mot
goal-agreement name ps fields ctor mot size =
  trans (subst-apps σ (shift ar 0 mot)
    (map (F.specializeParameters ar ps) (ctor-indices ctor)
      ++ tm-ctor name (surface-field-vars ar) ∷ []))
    (cong₂ Native.apps
      (trans (cong (λ k → substS σ (shift k 0 mot))
        (sym (trans (length-reverse fields) size))) (substS-argsSub-shift (reverse fields) mot))
      (trans (subst-append σ (map (F.specializeParameters ar ps) (ctor-indices ctor))
        (tm-ctor name (surface-field-vars ar) ∷ []))
        (cong₂ _++_ (staged-indices ps fields ar (ctor-indices ctor) size)
          (cong (λ xs → tm-ctor name xs ∷ []) (surface-fields fields ar size)))))
  where
    ar = length (ctor-args ctor)
    σ = argsSub (reverse fields)

module Preservation (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  module T = Transport.Transport ind sig conv

  SupportedBranches : ∀ {n} {Γ : Ctx n} {family ps mot brs}
    → Branches Γ family ps mot brs → Set
  SupportedBranches br[] = ⊤
  SupportedBranches (br∷ found owner opening wf checked rest) =
    T.Supported⇐ checked × SupportedBranches rest

  SelectedSupport : ∀ {n} {Γ : Ctx n} {family ps mot brs}
    → Name → Branches Γ family ps mot brs → Set
  SelectedSupport name br[] = ⊥
  SelectedSupport name (br∷ {name = cn} found owner opening wf checked rest) with name ≟ cn
  ... | yes equal = T.Supported⇐ checked
  ... | no different = SelectedSupport name rest

  select-support : ∀ {n} {Γ : Ctx n} {family ps mot brs name ar b}
    → (branches : Branches Γ family ps mot brs) → SupportedBranches branches
    → findBranch name brs ≡ just (name , ar , b) → SelectedSupport name branches
  select-support br[] good ()
  select-support {name = name}
    (br∷ {name = cn} entry owner opening wf checked rest) (gb , gr) found with name ≟ cn
  ... | yes equal = gb
  ... | no different = select-support rest gr found

  module Valid (valid : SignatureValid) where
    module V = T.Valid valid

    -- First-match lookup selects BOTH its actual body and its native
    -- constructor metadata. A later duplicate cannot supply the proof.
    selected-contract : ∀ {n} {Γ : Ctx n} {family ctor name ps fields mot brs ar b}
      → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      → (actual : Spine Γ (reverse ps) fields (ctor-args ctor))
      → T.SupportedSpine actual → FinalTerms fields
      → (branches : Branches Γ family ps mot brs) → SelectedSupport name branches
      → findBranch name brs ≡ just (name , ar , b)
      → length (ctor-args ctor) ≡ ar
        × T.Check Γ (substArgs fields b) (case-goal name ps fields ctor mot)
    selected-contract found actual supported finals br[] good ()
    selected-contract {name = name} {ps = ps} {fields = fields} {mot = mot}
      found actual supported finals
      (br∷ {name = cn} {ctor = ct} entry refl opening wf checked rest) good selected
      with name ≟ cn
    ... | yes refl with just-inj (trans (sym found) entry) | just-inj selected
    ... | refl | refl = refl ,
      T.cast⇐ refl (goal-agreement name ps fields ct mot (spine-length actual))
        (V.contract-branch {ps = ps} opening actual supported finals checked good)
    selected-contract {name = name} found actual supported finals
      (br∷ {name = cn} entry refl opening wf checked rest) good selected
      | no different = selected-contract found actual supported finals rest good selected

    -- Every field is a premise of the actual native source-case rule.
    -- Constructor/result parameters are shared explicitly; arbitrary
    -- conversion-based constructor inversion is not silently assumed.
    record SourceCase {n} (Γ : Ctx n) (name : Name) (ps fields : List Term)
      (mot : Term) (brs : List Branch) : Set where
      field
        family : Family
        ctor : Ctor
        found : findCtor name (IndEnv.families ind) ≡ just (family , ctor)
        caller : WellFormed Γ
        parameters : Spine Γ [] ps (fam-params family)
        arguments : Spine Γ (reverse ps) fields (ctor-args ctor)
        result-indices : Spine Γ (reverse ps)
          (F.instantiateResults ps fields (ctor-indices ctor)) (fam-indices family)
        level : Level
        motive-valid : Motive Γ family ps mot level
        branches : Branches Γ family ps mot brs
        coverage : CaseCoverage ind (fam-name family) brs

    source-typed : ∀ {n} {Γ : Ctx n} {name ps fields mot brs}
      → (source : SourceCase Γ name ps fields mot brs)
      → Γ ⊢ tm-case (tm-ctor name fields) mot brs
          ⇒ case-goal name ps fields (SourceCase.ctor source) mot
    source-typed source = ⇒-case (SourceCase.caller source)
      (SignatureValid.owner-visible valid (SourceCase.found source))
      (⇒-ctor (SourceCase.found source) (SourceCase.parameters source) (SourceCase.arguments source))
      (SourceCase.parameters source) (SourceCase.result-indices source)
      (SourceCase.motive-valid source) (SourceCase.branches source) (SourceCase.coverage source)

    preserve-selected-at : ∀ {n} {Γ : Ctx n} {name ps fields mot brs ar b goal}
      → (source : SourceCase Γ name ps fields mot brs)
      → T.SupportedSpine (SourceCase.arguments source) → FinalTerms fields
      → SelectedSupport name (SourceCase.branches source)
      → findBranch name brs ≡ just (name , ar , b)
      → Conversion._≈_ conv (case-goal name ps fields (SourceCase.ctor source) mot) goal
      → (Γ ⊢ tm-case (tm-ctor name fields) mot brs ⇐ goal)
        × (_⇝_ sig (tm-case (tm-ctor name fields) mot brs) (substArgs fields b))
        × T.Check Γ (substArgs fields b) goal
    preserve-selected-at {fields = fields} source supported finals gb selected equal
      with selected-contract (SourceCase.found source) (SourceCase.arguments source)
        supported finals (SourceCase.branches source) gb selected
    ... | arity , checked = ⇐-infer (source-typed source) equal ,
      ι selected (trans (spine-length (SourceCase.arguments source)) arity) ,
      (⇐-conv (proj₁ checked) equal , proj₂ checked)

    -- Convenience entry point when all branch bodies belong to the
    -- fragment. The primary theorem does not restrict unused bodies.
    preserve-at : ∀ {n} {Γ : Ctx n} {name ps fields mot brs ar b goal}
      → (source : SourceCase Γ name ps fields mot brs)
      → T.SupportedSpine (SourceCase.arguments source) → FinalTerms fields
      → SupportedBranches (SourceCase.branches source)
      → findBranch name brs ≡ just (name , ar , b)
      → Conversion._≈_ conv (case-goal name ps fields (SourceCase.ctor source) mot) goal
      → (Γ ⊢ tm-case (tm-ctor name fields) mot brs ⇐ goal)
        × (_⇝_ sig (tm-case (tm-ctor name fields) mot brs) (substArgs fields b))
        × T.Check Γ (substArgs fields b) goal
    preserve-at source supported finals good selected equal =
      preserve-selected-at source supported finals
        (select-support (SourceCase.branches source) good selected) selected equal
