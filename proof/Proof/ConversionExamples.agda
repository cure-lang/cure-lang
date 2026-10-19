------------------------------------------------------------------------
-- Inhabited conversion-record and typing regressions.
-- The zeta-only model is intentionally NOT a full preservation/soundness
-- model: a checked negative control rejects full ReduceConv below.
------------------------------------------------------------------------
module Proof.ConversionExamples where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Core.Grade using (unrestricted; erased)
open import Core.Universe using (l0; l1; _≤ˡ_; l0≤l1)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Signature using (fam-name; IndEnv)
open import Core.Reduction using (Signature; β; ζ; _⇝_)
open import Core.Typing using (Conversion; ⟨⟩)
open import Proof.Inversion using (IsLam; module Invert)
open import Proof.Values using (Canonical)
open import Proof.Preservation using (ReduceConv)
open import Proof.ConversionModel
import Proof.CoverageExamples as Cases

open Core.Typing.Typing Cases.env Cases.sig model
open Invert Cases.env Cases.sig model

pi-type : Term
pi-type = tm-pi unrestricted tm-int_type tm-int_type

let-pi : Term
let-pi = tm-let unrestricted (tm-type l0) pi-type (tm-var 0)

let-pi-converts : let-pi ≃ pi-type
let-pi-converts = refl

let-does-not-have-rigid-head : ∀ {h} → HasTypeHead let-pi h → ⊥
let-does-not-have-rigid-head ()

let-is-not-pi-syntax : ∀ g d c → let-pi ≡ tm-pi g d c → ⊥
let-is-not-pi-syntax g d c ()

-- Exercise the active generalized inverter through an intermediate type
-- that really is a let, in both inference and checking modes.
int-id : Term
int-id = tm-lam unrestricted tm-int_type (tm-var 0)

id-infers : ⟨⟩ ⊢ int-id ⇒ pi-type
id-infers = ⇒-lam ⇒-int_type (⇐-infer (⇒-var Fin.zero) refl)

id-let-type : ⟨⟩ ⊢ int-id ⇒ let-pi
id-let-type = ⇒-conv id-infers (sym let-pi-converts)

id-roundtrip : ⟨⟩ ⊢ int-id ⇒ pi-type
id-roundtrip = ⇒-conv id-let-type let-pi-converts

inversion-through-let : IsLam int-id
inversion-through-let = invert-pi c-lam id-roundtrip

checked-let-type : ⟨⟩ ⊢ int-id ⇐ let-pi
checked-let-type = ⇐-conv (⇐-infer {T = pi-type} id-infers refl) (sym let-pi-converts)

checked-inversion-through-let : IsLam int-id
checked-inversion-through-let =
  invert-pi-check 0 ⟨⟩ {g = unrestricted} {d = tm-int_type} {c = tm-int_type}
    (⇐-conv checked-let-type let-pi-converts) c-lam

let-nat : Term
let-nat = tm-let unrestricted (tm-type l0) Cases.nat-type (tm-var 0)

literal-through-let : ⟨⟩ ⊢ tm-nat_lit 17 ⇒ Cases.nat-type
literal-through-let = ⇒-conv (⇒-conv {T′ = let-nat} (⇒-nat_lit refl) refl) refl

literal-owner : IndEnv.builtins Cases.env "nat" ≡ just "Nat"
literal-owner = nat-data-family literal-through-let

constructor-through-let : ⟨⟩ ⊢ tm-ctor "Z" [] ⇒ Cases.nat-type
constructor-through-let = ⇒-conv (⇒-conv {T′ = let-nat} (⇒-ctor refl ⊢*[]) refl) refl

constructor-owner :
  fam-name (proj₁ (constructor-data constructor-through-let)) ≡ "Nat"
constructor-owner = proj₁ (proj₂ (proj₂ (proj₂ (constructor-data constructor-through-let))))
global-types : Name → Maybe Term
global-types "identity" = just let-pi
global-types _ = nothing

global-sig : Signature
global-sig = record { body = λ _ → nothing ; type-of = global-types }

module Globals = Core.Typing.Typing Cases.env global-sig model

global-with-let-type :
  Globals._⊢_⇒_ ⟨⟩ (tm-global "identity") let-pi
global-with-let-type = Globals.⇒-global refl

global-exposes-pi :
  Globals._⊢_⇒_ ⟨⟩ (tm-global "identity") pi-type
global-exposes-pi = Globals.⇒-conv global-with-let-type let-pi-converts

-- Exact levels are an invariant of EVERY repaired Conversion record,
-- not just of this particular bounded model.
sorts-not-equal : ∀ conv → Conversion._≈_ conv (tm-type l0) (tm-type l1) → ⊥
sorts-not-equal conv eq with Conversion.≈-heads conv ty-universe ty-universe eq
... | ()

upward-typing : ⟨⟩ ⊢ tm-int_type ⇒ tm-type l1
upward-typing = ⇒-cumul ⇒-int_type l0≤l1

upward-checking : ⟨⟩ ⊢ tm-int_type ⇐ tm-type l1
upward-checking = ⇐-cumul ⇒-int_type l0≤l1

no-downward-inclusion : l1 ≤ˡ l0 → ⊥
no-downward-inclusion ()

grades-not-equal : tm-pi erased tm-int_type tm-int_type ≃ pi-type → ⊥
grades-not-equal ()

families-not-equal : Cases.nat-type ≃ tm-data "Bool" [] [] → ⊥
families-not-equal ()

holes-not-equal : tm-hole "left" ≃ tm-hole "right" → ⊥
holes-not-equal ()

-- Coarse value equality is deliberate: this witness establishes record
-- satisfiability, NOT faithful constructor/literal conversion.
coarse-values : tm-ctor "Z" [] ≃ tm-nat_lit 99
coarse-values = refl

beta-redex : Term
beta-redex = tm-app int-id (tm-int_lit (pos 7))

beta-redex-typed : ⟨⟩ ⊢ beta-redex ⇒ tm-int_type
beta-redex-typed = ⇒-app id-roundtrip ⇒-int_lit

beta-not-in-model : beta-redex ≃ tm-int_lit (pos 7) → ⊥
beta-not-in-model ()

no-full-reduction-instance : ReduceConv Cases.sig model → ⊥
no-full-reduction-instance rc =
  beta-not-in-model (rc {t = beta-redex} {t′ = tm-int_lit (pos 7)} β)

-- The exact let/Pi counterexample is now allowed without raw reflection.
zeta-step : _⇝_ Cases.sig let-pi pi-type
zeta-step = ζ

zeta-step-converts : let-pi ≃ pi-type
zeta-step-converts = model-zeta unrestricted (tm-type l0) pi-type (tm-var 0)
