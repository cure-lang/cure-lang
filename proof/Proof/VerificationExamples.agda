------------------------------------------------------------------------
-- Inhabited examples for the candidate verification interfaces.
-- No legacy Covers/ClosedSig/Conversion/LiteralArity hypothesis is used.
-- This is NOT an instance of the unrepaired full soundness theorem.
------------------------------------------------------------------------
module Proof.VerificationExamples where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (zero; suc; z≤n; s≤s)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Verification

dependent-ctor : Ctor
dependent-ctor = record
  { ctor-name = "Pack"
  ; ctor-args = ("A" , tm-type l0) ∷ ("x" , tm-var zero) ∷ []
  ; ctor-params = []
  ; ctor-indices = tm-var (suc zero) ∷ []
  }

dependent-family : Family
dependent-family = record
  { fam-name = "Packed"
  ; fam-params = []
  ; fam-indices = ("A" , tm-type l0) ∷ []
  ; fam-level = l1
  ; fam-ctors = dependent-ctor ∷ []
  ; universe-ok = true
  ; positive = true
  }

-- This witness establishes SCOPING, not declaration typing/universe
-- validity. The Boolean declaration flags are not verification proofs.
dependent-scoped : ScopedFamily dependent-family
dependent-scoped = tele[] , tele∷ sc-type tele[] , ct-scoped
  where
    ct-scoped : ∀ ct → ct ∈ (dependent-ctor ∷ [])
      → ScopedCtor zero ct
    ct-scoped .dependent-ctor (here refl) =
        tele∷ sc-type (tele∷ (sc-var (s≤s z≤n)) tele[])
      , st[]
      , st∷ (sc-var (s≤s (s≤s z≤n))) st[]
    ct-scoped ct (there ())

-- A raw dependent entry is not required to be closed.
dependent-entry-not-closed : Scoped zero (tm-var zero) → ⊥
dependent-entry-not-closed (sc-var ())

covered-branches : List Branch
covered-branches = ("Pack" , 2 , tm-var zero) ∷ []

dependent-covered : FamilyCoverage dependent-family covered-branches
dependent-covered .dependent-ctor (here refl) = tm-var zero , refl
dependent-covered ct (there ())

missing-branch-rejected : FamilyCoverage dependent-family [] → ⊥
missing-branch-rejected covered with covered dependent-ctor (here refl)
... | b , ()

wrong-arity-rejected :
  FamilyCoverage dependent-family (("Pack" , 1 , tm-var zero) ∷ []) → ⊥
wrong-arity-rejected covered with covered dependent-ctor (here refl)
... | b , ()

empty-family : Family
empty-family = record
  { fam-name = "Empty"
  ; fam-params = []
  ; fam-indices = []
  ; fam-level = l0
  ; fam-ctors = []
  ; universe-ok = true
  ; positive = true
  }

empty-elimination-covered : FamilyCoverage empty-family []
empty-elimination-covered ct ()

-- Distinguishable fields detect reversal errors, unlike repeated values.
field-zero-is-last :
  instantiateFields (tm-nat_lit 11 ∷ tm-nat_lit 22 ∷ []) (tm-var zero)
    ≡ tm-nat_lit 22
field-zero-is-last = refl

field-one-is-first :
  instantiateFields (tm-nat_lit 11 ∷ tm-nat_lit 22 ∷ []) (tm-var 1)
    ≡ tm-nat_lit 11
field-one-is-first = refl

fields-preserve-outer-index :
  instantiateFields (tm-nat_lit 11 ∷ tm-nat_lit 22 ∷ []) (tm-var 2)
    ≡ tm-var zero
fields-preserve-outer-index = refl

result-index-instantiated :
  instantiateIndices dependent-ctor (tm-int_type ∷ tm-int_lit (pos 42) ∷ [])
    ≡ tm-int_type ∷ []
result-index-instantiated = refl

-- A concrete nonempty signature admits a declared type whose syntax is
-- a let rather than a Pi. No global literal-head reflection is assumed.
pi-type : Term
pi-type = tm-pi unrestricted tm-int_type tm-int_type

let-pi : Term
let-pi = tm-let unrestricted (tm-type l0) pi-type (tm-var zero)

identity : Term
identity = tm-lam unrestricted tm-int_type (tm-var zero)

example-sig : Signature
example-sig = record { body = λ _ → just identity ; type-of = λ _ → just let-pi }

example-ind : IndEnv
example-ind = record { families = dependent-family ∷ [] ; builtins = λ _ → nothing }

signature-scoped : ScopedSignature example-ind example-sig
signature-scoped = global-scoped , family-scoped
  where
    global-scoped : ∀ name {ty}
      → Signature.type-of example-sig name ≡ just ty → Scoped zero ty
    global-scoped name refl =
      sc-let sc-type (sc-pi sc-int_type sc-int_type) (sc-var (s≤s z≤n))

    family-scoped : ∀ f → f ∈ (dependent-family ∷ [])
      → ScopedFamily f
    family-scoped .dependent-family (here refl) = dependent-scoped
    family-scoped f (there ())

let-exposes-pi : PiExposure example-sig let-pi
let-exposes-pi = unrestricted , tm-int_type , tm-int_type , ⇝*-step ζ ⇝*-refl
