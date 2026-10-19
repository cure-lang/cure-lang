------------------------------------------------------------------------
-- The membership-indexed CLOSED fragment is inhabited.
-- These are signature-invariant examples, not an instance of full Cure
-- soundness or a proof that the old dependent typing rules are faithful.
------------------------------------------------------------------------
module Proof.ClosedFragmentExamples where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (_∈Tele_; ∈-here; ∈-there)
open import Core.ClosedFragment
open import Core.Verification using (ScopedFamily)
import Proof.CoverageExamples as Cases
import Proof.VerificationExamples as Dependent

identity-type : Term
identity-type = tm-pi unrestricted Cases.nat-type Cases.nat-type

identity-type-closed : Scoped 0 identity-type
identity-type-closed = sc-pi (sc-data st[] st[]) (sc-data st[] st[])

global-type : Name → Maybe Term
global-type name with name ≟ "identity"
... | yes eq = just identity-type
... | no neq = nothing

sig : Signature
sig = record { body = λ _ → nothing ; type-of = global-type }

global-closed : ∀ name {T} → Signature.type-of sig name ≡ just T → Scoped 0 T
global-closed name eq with name ≟ "identity"
... | yes same = subst (Scoped 0) (just-inj eq) identity-type-closed
... | no different = ⊥-elim (nothing≠just eq)

params-closed : ∀ f → f ∈ IndEnv.families Cases.env
  → ∀ {T} → T ∈Tele (fam-params f) → Scoped 0 T
params-closed f (here refl) ()
params-closed f (there (here refl)) ()
params-closed f (there (there (here refl))) ()
params-closed f (there (there (there ()))) entry

indices-closed : ∀ f → f ∈ IndEnv.families Cases.env
  → ∀ {T} → T ∈Tele (fam-indices f) → Scoped 0 T
indices-closed f (here refl) ()
indices-closed f (there (here refl)) ()
indices-closed f (there (there (here refl))) ()
indices-closed f (there (there (there ()))) entry

args-closed : ∀ f → f ∈ IndEnv.families Cases.env
  → ∀ ct → ct ∈ fam-ctors f
  → ∀ {T} → T ∈Tele (ctor-args ct) → Scoped 0 T
args-closed f (here refl) ct (here refl) ()
args-closed f (here refl) ct (there (here refl)) ∈-here = sc-data st[] st[]
args-closed f (here refl) ct (there (here refl)) (∈-there ())
args-closed f (here refl) ct (there (there ())) entry
args-closed f (there (here refl)) ct (here refl) ()
args-closed f (there (here refl)) ct (there (here refl)) ()
args-closed f (there (here refl)) ct (there (there ())) entry
args-closed f (there (there (here refl))) ct () entry
args-closed f (there (there (there ()))) ct member entry

result-closed : ∀ f → f ∈ IndEnv.families Cases.env
  → ∀ ct → ct ∈ fam-ctors f
  → Scoped 0 (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
result-closed f (here refl) ct (here refl) = sc-data st[] st[]
result-closed f (here refl) ct (there (here refl)) = sc-data st[] st[]
result-closed f (here refl) ct (there (there ()))
result-closed f (there (here refl)) ct (here refl) = sc-data st[] st[]
result-closed f (there (here refl)) ct (there (here refl)) = sc-data st[] st[]
result-closed f (there (here refl)) ct (there (there ()))
result-closed f (there (there (here refl))) ct ()
result-closed f (there (there (there ()))) ct member

closed-signature : ClosedFragmentSig Cases.env sig
closed-signature =
  global-closed , params-closed , indices-closed , args-closed , result-closed

-- The positive instance is nonempty in both families and global types.
identity-registered : Signature.type-of sig "identity" ≡ just identity-type
identity-registered = refl

nat-registered : findFamily "Nat" (IndEnv.families Cases.env) ≡ just Cases.nat-family
nat-registered = refl

open-family : Family
open-family = record
  { fam-name = "Open" ; fam-params = ("x" , tm-var 0) ∷ []
  ; fam-indices = [] ; fam-level = l0 ; fam-ctors = []
  ; universe-ok = true ; positive = true }

unregistered-open-family : open-family ∈ IndEnv.families Cases.env → ⊥
unregistered-open-family (here ())
unregistered-open-family (there (here ()))
unregistered-open-family (there (there (here ())))
unregistered-open-family (there (there (there ())))

var0-not-closed : Scoped 0 (tm-var 0) → ⊥
var0-not-closed (sc-var ())

registered-open-env : IndEnv
registered-open-env = record { families = open-family ∷ [] ; builtins = λ _ → nothing }

registered-open-family-rejected : ClosedFragmentSig registered-open-env sig → ⊥
registered-open-family-rejected closed =
  var0-not-closed (proj₁ (proj₂ closed) open-family (here refl) ∈-here)

open-ctor : Ctor
open-ctor = record
  { ctor-name = "OpenCtor" ; ctor-args = ("x" , tm-var 0) ∷ []
  ; ctor-params = [] ; ctor-indices = [] }

unregistered-open-ctor : open-ctor ∈ fam-ctors Cases.nat-family → ⊥
unregistered-open-ctor (here ())
unregistered-open-ctor (there (here ()))
unregistered-open-ctor (there (there ()))

bad-ctor-family : Family
bad-ctor-family = record
  { fam-name = "BadCtor" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = open-ctor ∷ [] ; universe-ok = true ; positive = true }

bad-ctor-env : IndEnv
bad-ctor-env = record { families = bad-ctor-family ∷ [] ; builtins = λ _ → nothing }

registered-open-ctor-rejected : ClosedFragmentSig bad-ctor-env sig → ⊥
registered-open-ctor-rejected closed =
  var0-not-closed (proj₁ (proj₂ (proj₂ (proj₂ closed)))
    bad-ctor-family (here refl) open-ctor (here refl) ∈-here)

open-result-ctor : Ctor
open-result-ctor = record
  { ctor-name = "OpenResult" ; ctor-args = []
  ; ctor-params = [] ; ctor-indices = tm-var 0 ∷ [] }

bad-result-family : Family
bad-result-family = record
  { fam-name = "BadResult" ; fam-params = [] ; fam-indices = []
  ; fam-level = l0 ; fam-ctors = open-result-ctor ∷ []
  ; universe-ok = true ; positive = true }

bad-result-env : IndEnv
bad-result-env = record { families = bad-result-family ∷ [] ; builtins = λ _ → nothing }

open-result-not-closed : Scoped 0 (tm-data "BadResult" [] (tm-var 0 ∷ [])) → ⊥
open-result-not-closed (sc-data st[] (st∷ (sc-var ()) rest))

registered-open-result-rejected : ClosedFragmentSig bad-result-env sig → ⊥
registered-open-result-rejected closed =
  open-result-not-closed (proj₂ (proj₂ (proj₂ (proj₂ closed)))
    bad-result-family (here refl) open-result-ctor (here refl))

-- A genuine scoped dependent telescope belongs to the future interface,
-- but NOT to this individually-closed-entry fragment. Do not weaken this
-- negative control to make the unfinished dependent proof look complete.
dependent-env : IndEnv
dependent-env = record { families = Dependent.dependent-family ∷ []
                       ; builtins = λ _ → nothing }

dependent-scoping-is-inhabited : ScopedFamily Dependent.dependent-family
dependent-scoping-is-inhabited = Dependent.dependent-scoped

dependent-not-closed-fragment : ClosedFragmentSig dependent-env sig → ⊥
dependent-not-closed-fragment closed =
  var0-not-closed (proj₁ (proj₂ (proj₂ (proj₂ closed)))
    Dependent.dependent-family (here refl) Dependent.dependent-ctor (here refl)
    (∈-there ∈-here))
