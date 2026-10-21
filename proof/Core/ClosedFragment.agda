------------------------------------------------------------------------
-- Signature invariant for the CURRENT closed-telescope proof fragment.
--
-- Unlike the historical ClosedSig oracle, only actual signature members
-- are constrained. Individual entries and constructor results must still
-- be closed: this is NOT the scoped dependent-telescope invariant in
-- Core.Verification, nor a proof that dependent constructor typing works.
------------------------------------------------------------------------
module Core.ClosedFragment where

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (_×_)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (_∈Tele_)

ClosedFragmentSig : IndEnv → Signature → Set
ClosedFragmentSig ind sig =
    (∀ name {T} → Signature.type-of sig name ≡ just T → Scoped 0 T)
  × (∀ f → f ∈ IndEnv.families ind
     → ∀ {T} → T ∈Tele (fam-params f) → Scoped 0 T)
  × (∀ f → f ∈ IndEnv.families ind
     → ∀ {T} → T ∈Tele (fam-indices f) → Scoped 0 T)
  × (∀ f → f ∈ IndEnv.families ind
     → ∀ ct → ct ∈ fam-ctors f
     → ∀ {T} → T ∈Tele (ctor-args ct) → Scoped 0 T)
  × (∀ f → f ∈ IndEnv.families ind
     → ∀ ct → ct ∈ fam-ctors f
     → Scoped 0 (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct)))

-- A successful family lookup justifies using the invariant at that family.
family-lookup-member : ∀ {name fs f}
  → findFamily name fs ≡ just f → f ∈ fs
family-lookup-member {fs = []} ()
family-lookup-member {name} {f₀ ∷ fs} found with name ≟ fam-name f₀
... | yes refl = here (sym (just-inj found))
... | no neq = there (family-lookup-member {fs = fs} found)
