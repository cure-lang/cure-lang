------------------------------------------------------------------------
-- Candidate verification interfaces for the soundness repair.
--
-- These predicates have concrete instances in Proof.VerificationExamples.
-- ScopedTele now supports Proof.DependentSpine's kind-checked judgment and
-- the local frame has agreement proofs. Constructor/branch admission and
-- head-exposure remain prototypes, not an executable refinement. Coverage is
-- now in Core.Coverage and is required by Core.Typing's ⇒-case rule.
------------------------------------------------------------------------
module Core.Verification where

open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; ∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core.Grade using (Grade)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
import Core.LocalFrame as Frame

-- Full-family coverage of THIS branch list. Indexed omission of an
-- impossible constructor is deliberately not part of this first interface.
FamilyCoverage : Family → List Branch → Set
FamilyCoverage f brs =
  ∀ ct → ct ∈ fam-ctors f
  → ∃ λ b
  → findBranch (ctor-name ct) brs ≡ just (ctor-name ct , length (ctor-args ct) , b)

coverage-rename : ∀ f brs ρ
  → FamilyCoverage f brs → FamilyCoverage f (renameBranches ρ brs)
coverage-rename f brs ρ covered ct member with covered ct member
... | b , found = _ , findBranch-rename ρ (ctor-name ct) brs found

coverage-subst : ∀ f brs σ
  → FamilyCoverage f brs → FamilyCoverage f (substBranchesS σ brs)
coverage-subst f brs σ covered ct member with covered ct member
... | b , found = _ , findBranch-substBranchesS σ (ctor-name ct) brs found

-- Telescope entries are scoped relative to all PRECEDING binders.
-- For example (A : Type 0, x : A) is valid at depth zero, although its
-- second entry is not a closed term.
data ScopedTele : ℕ → Telescope → Set where
  tele[] : ∀ {d} → ScopedTele d []
  tele∷ : ∀ {d name ty rest}
    → Scoped d ty → ScopedTele (suc d) rest
    → ScopedTele d ((name , ty) ∷ rest)

ScopedCtor : ℕ → Ctor → Set
ScopedCtor parameters ct =
    ScopedTele parameters (ctor-args ct)
  × ScopedTerms (length (ctor-args ct) + parameters) (ctor-params ct)
  × ScopedTerms (length (ctor-args ct) + parameters) (ctor-indices ct)

ScopedFamily : Family → Set
ScopedFamily f =
    ScopedTele zero (fam-params f)
  × ScopedTele (length (fam-params f)) (fam-indices f)
  × (∀ ct → ct ∈ fam-ctors f → ScopedCtor (length (fam-params f)) ct)

-- Only actual signature members are constrained, not arbitrary records.
ScopedSignature : IndEnv → Signature → Set
ScopedSignature ind sig =
    (∀ name {ty} → Signature.type-of sig name ≡ just ty → Scoped zero ty)
  × (∀ f → f ∈ IndEnv.families ind → ScopedFamily f)

-- The executable evaluates branches under reverse(fields) ++ base-env:
-- the last field has de Bruijn index zero. The legacy substArgs has the
-- opposite convention and must not be used for this interface.
instantiateFields : List Term → Term → Term
instantiateFields = Frame.instantiateFields

instantiateIndices : Ctor → List Term → List Term
instantiateIndices ct fields = Data.List.map (Frame.instantiateFields fields) (ctor-indices ct)

instantiateIndicesWithParameters : Ctor → List Term → List Term → List Term
instantiateIndicesWithParameters ct parameters fields =
  Frame.instantiateResults parameters fields (ctor-indices ct)

instantiateParameters : Ctor → List Term → List Term → List Term
instantiateParameters ct parameters fields =
  Frame.instantiateResults parameters fields (ctor-params ct)

-- An exposed head is reached by reduction, not identified with raw syntax.
-- These are evidence types, NOT assumed reflection laws of an arbitrary
-- relation. Proving conversion implies such exposure remains an obligation.
PiExposure : Signature → Term → Set
PiExposure sig ty =
  Σ Grade (λ g → Σ Term (λ d → Σ Term (λ c → _⇝*_ sig ty (tm-pi g d c))))

DataExposure : Signature → Term → Set
DataExposure sig ty =
  Σ Name (λ name → Σ (List Term) (λ ps → Σ (List Term)
    (λ is → _⇝*_ sig ty (tm-data name ps is))))
