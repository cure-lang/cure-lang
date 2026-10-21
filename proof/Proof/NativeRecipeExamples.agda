{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Recipes are plain untrusted data. Three exported globals replay;
-- the dependent case proof remains MANUAL in the mixed certificate.
-- No byte parser, Elixir producer or whole-kernel refinement is claimed.
------------------------------------------------------------------------
module Proof.NativeRecipeExamples where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Typing using (⟨⟩)
open import Core.Reduction
open import Core.Signature
import Data.Bool as Bool
import Proof.ReductionConversion as Reduction
open import Core.NativeRecipe
import Proof.ExecutableSnapshotExamples as Input
import Proof.NativeCertificateExamples as E
import Proof.NativeCertificateSafety as Existing
import Proof.DependentSoundness as Safety
import Fixtures.ExecutableSnapshot as Fixture

present : ∀ {A : Set} → Maybe A → Bool
present nothing = false
present (just value) = true
require : ∀ {A : Set} (result : Maybe A) → present result ≡ true → A
require nothing ()
require (just value) accepted = value

module G = Globals Fixture.source Input.accepted Input.replayed E.conv
module D = G.D

scalar-packet packed-packet : Packet
scalar-packet = packet r-leaf (just r-leaf)
packed-packet = packet (r-data [] (r-leaf ∷ []))
  (just (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])))
answer : G.C.GlobalEvidence Input.raw-answer
answer = require (G.replay Input.raw-answer scalar-packet) refl
held : G.C.GlobalEvidence Input.raw-held
held = require (G.replay Input.raw-held scalar-packet) refl
packed : G.C.GlobalEvidence Input.raw-packed
packed = require (G.replay Input.raw-packed packed-packet) refl
case-not-replayed : present (G.replay Input.raw-unpack scalar-packet) ≡ false
case-not-replayed = refl

computed-index-proof : E.N._⊢_⇒_ E.Φ E.computed-index (tm-type l0)
computed-index-proof = require
  (D.at E.Φ E.computed-index (tm-type l0) (r-app (r-lam r-leaf r-leaf) r-leaf)) refl

dependent-pi dependent-lambda : Term
dependent-pi = tm-pi unrestricted (tm-type l0)
  (tm-pi unrestricted (tm-var 0) (tm-var 1))
dependent-lambda = tm-lam unrestricted (tm-type l0)
  (tm-lam unrestricted (tm-var 0) (tm-var 0))
pi-kind : E.N._⊢_⇒_ ⟨⟩ dependent-pi (tm-type l1)
pi-kind = require (D.at ⟨⟩ dependent-pi (tm-type l1) (r-pi r-leaf (r-pi r-leaf r-leaf))) refl
lambda-typed : E.N._⊢_⇒_ ⟨⟩ dependent-lambda dependent-pi
lambda-typed = require
  (D.at ⟨⟩ dependent-lambda dependent-pi (r-lam r-leaf (r-lam r-leaf r-leaf))) refl

let-typed : E.N._⊢_⇒_ ⟨⟩
  (tm-let unrestricted tm-atom_type (tm-atom_lit "v") (tm-var 0)) tm-atom_type
let-typed = require
  (D.at ⟨⟩ (tm-let unrestricted tm-atom_type (tm-atom_lit "v") (tm-var 0))
    tm-atom_type (r-let r-leaf r-leaf r-leaf)) refl
global-typed : E.N._⊢_⇒_ ⟨⟩ (tm-global "Boundary#packed") E.goal
global-typed = require (D.at ⟨⟩ (tm-global "Boundary#packed") E.goal r-leaf) refl

-- A separate small parameter-bearing registry exercises a real nonempty
-- witness. No automatic certificate for this registry is claimed.
box-ctor : Ctor
box-ctor = record
  { ctor-name = "Recipe#BoxValue" ; ctor-args = ("x" , tm-var 0) ∷ []
  ; ctor-params = tm-var 1 ∷ [] ; ctor-indices = [] }
box-family : Family
box-family = record
  { fam-name = "Recipe#Box" ; fam-params = ("A" , tm-type l0) ∷ [] ; fam-indices = []
  ; fam-level = l0 ; fam-ctors = box-ctor ∷ []
  ; positive = Bool.false ; universe-ok = Bool.false }
box-ind : IndEnv
box-ind = record { families = box-family ∷ [] ; builtins = λ _ → nothing }
box-sig : Signature
box-sig = record { type-of = λ _ → nothing ; body = λ _ → nothing }
module BoxConversion = Reduction.Model box-sig (λ ())
module Box = Derive box-ind box-sig BoxConversion.conversion
box-typed : Box.N._⊢_⇒_ ⟨⟩ (tm-ctor "Recipe#BoxValue" (tm-atom_lit "v" ∷ []))
  (tm-data "Recipe#Box" (tm-atom_type ∷ []) [])
box-typed = require
  (Box.at ⟨⟩ (tm-ctor "Recipe#BoxValue" (tm-atom_lit "v" ∷ []))
    (tm-data "Recipe#Box" (tm-atom_type ∷ []) [])
    (r-ctor (tm-atom_type ∷ []) (r-leaf ∷ []) (r-leaf ∷ []))) refl
wrong-parameter-seed : present
  (Box.infer ⟨⟩ (tm-ctor "Recipe#BoxValue" (tm-atom_lit "v" ∷ []))
    (r-ctor (tm-float_type ∷ []) (r-leaf ∷ []) (r-leaf ∷ []))) ≡ false
wrong-parameter-seed = refl

-- This is intentionally mixed, not a claim that all four globals or
-- declaration certificates have been produced from untrusted recipes.
mixed-evidence : G.C.Evidence
mixed-evidence = record
  { families = E.C.Evidence.families E.evidence
  ; definitions = answer All.∷ held All.∷ packed All.∷
      All.lookup (E.C.Evidence.definitions E.evidence) (there (there (there (here refl)))) All.∷ All.[] }
mixed-valid : E.N.SignatureValid
mixed-valid = G.C.validity mixed-evidence
mixed-program-admitted : E.N.Admitted ⟨⟩ E.program tm-atom_type
mixed-program-admitted = G.C.admitted mixed-evidence {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl
mixed-program-eligible : G.C.A.Eligible ⟨⟩ E.program tm-atom_type
mixed-program-eligible = G.C.eligible mixed-evidence {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl

specification : Safety.Specification E.ind E.sig E.conv
specification = record Existing.specification
  { signature-valid = mixed-valid
  ; reduction-converts = λ {t} {u} → Input.ConversionModel.reduce-converts {t = t} {u = u}
  ; global-bodies-final = λ {name} → Input.visible-bodies-final {name} }
module Sound = Safety.Sound E.ind E.sig E.conv specification
mixed-safe : Sound.SafeState (tm-atom_lit "payload") tm-atom_type
mixed-safe = Sound.trace-safe
  (G.C.A.Eligible.checked mixed-program-eligible)
  (G.C.A.Eligible.source-final mixed-program-eligible)
  (⇝*-step (ι refl refl) ⇝*-refl)
