{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Recipes are plain untrusted data. Three exported globals replay;
-- the dependent case proof remains MANUAL in the mixed certificate.
-- GOAL-DIRECTED CONVERSION IS NOW REPLAYED: recipes certify β/ζ/δ and
-- congruence steps, so β-converted goals no longer fail on syntax alone.
-- No byte parser, Elixir producer or η/NbE refinement is claimed.
------------------------------------------------------------------------
module Proof.NativeRecipeExamples where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Signature
open import Core.Reduction
import Data.Bool as Bool
open import Proof.Confluence using (ClosedBody)
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
  Input.ConversionModel.reduce-converts
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

------------------------------------------------------------------------
-- CHECKED NON-REFLEXIVE CONVERSION
--
-- Each goal below is STRUCTURALLY different from the type the recipe
-- actually synthesizes, so the exact-syntax protocol alone rejected it
-- (the corresponding failures are retained in Proof.NativeRecipeControls).
-- The replayed result is a real native `⇒-conv` node: the conversion
-- witness is RECONSTRUCTED from β/ζ steps and the Conversion laws, and no
-- derivation, reduct or lookup is supplied as recipe data.
------------------------------------------------------------------------

beta-type : Term
beta-type = tm-app (tm-lam unrestricted tm-atom_type tm-atom_type) (tm-atom_lit "argument")

-- Synthesis gives `atom_type`; the goal is the unreduced β-redex.
beta-goal-replayed : E.N._⊢_⇒_ ⟨⟩ (tm-atom_lit "v") beta-type
beta-goal-replayed = require
  (D.at ⟨⟩ (tm-atom_lit "v") beta-type (r-convert beta-type (c-sym c-beta) r-leaf)) refl

-- Two DIFFERENT reductions, joined through an ASSERTED (and checked)
-- intermediate term: `let` reaches the sort by ζ, the redex by β.
let-type : Term
let-type = tm-let unrestricted tm-atom_type (tm-atom_lit "argument") tm-atom_type
beta-let-converts : Conversion._≈_ E.conv let-type beta-type
beta-let-converts = require
  (D.conversion let-type beta-type
    (c-trans tm-atom_type c-zeta (c-sym c-beta))) refl

-- Conversion UNDER A BINDER: the Π codomain is the β-redex, so the λ
-- cannot be checked by structural equality of the synthesized Π.
pi-goal : Term
pi-goal = tm-pi unrestricted tm-atom_type beta-type
lambda-replayed : E.N._⊢_⇐_ ⟨⟩ (tm-lam unrestricted tm-atom_type (tm-atom_lit "v")) pi-goal
lambda-replayed = require
  (D.checking ⟨⟩ (tm-lam unrestricted tm-atom_type (tm-atom_lit "v")) pi-goal
    (r-convert pi-goal (c-pi c-refl (c-sym c-beta)) (r-lam r-leaf r-leaf))) refl

-- DEPENDENT RESULT INDEX. `Boundary#Alternate` computes its index as
-- `(λ A → A) A`, so the synthesized data type index is a β-redex while the
-- declared goal index is the reduced form.
computed-value : Term
computed-value = tm-ctor "Boundary#Alternate" (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
computed-value-replayed : E.N._⊢_⇒_ ⟨⟩ computed-value E.goal
computed-value-replayed = require
  (D.at ⟨⟩ computed-value E.goal
    (r-convert E.goal (c-data [] (c-beta ∷ []))
      (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])))) refl

-- Compact-literal identification is a Conversion law, not a reduction:
-- the replayer must not decide literal equality on its own.
zero-identified : Conversion._≈_ E.conv (tm-ctor "Z" []) (tm-nat_lit 0)
zero-identified = require
  (D.conversion (tm-ctor "Z" []) (tm-nat_lit 0) c-nat-zero) refl
successor-identified : Conversion._≈_ E.conv (tm-ctor "S" (tm-nat_lit 0 ∷ [])) (tm-nat_lit 1)
successor-identified = require
  (D.conversion (tm-ctor "S" (tm-nat_lit 0 ∷ [])) (tm-nat_lit 1) c-nat-suc) refl

------------------------------------------------------------------------
-- δ REPLAY AGAINST AN ACTUAL SIGNATURE LOOKUP
--
-- The recipe carries only a NAME. The unfolding is obtained from the
-- signature supplied to the replayer, exactly like a global leaf; an
-- absent body makes the whole replay fail. This is the specification δ
-- rule, whose only premise is the body equation: it is NOT the kernel's
-- certification-gated unfolding.
------------------------------------------------------------------------

alias-redex-type : Term
alias-redex-type = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) (tm-type l0)

-- `Alias#kind` declares a type that is a β-REDEX, not a sort. Every
-- other alias declares the sort itself.
alias-type : Name → Maybe Term
alias-type "Alias#kind" = just alias-redex-type
alias-type other = just (tm-type l0)

-- A TOTAL body table: every alias unfolds to the same closed type. A total
-- table keeps the closed-body obligation honest and trivial; the MISSING
-- body control is exercised against the snapshot signature instead.
alias-body : Name → Maybe Term
alias-body other = just tm-atom_type

alias-sig : Signature
alias-sig = record { type-of = alias-type ; body = alias-body }
alias-closed : ClosedBody alias-sig
alias-closed {f = key} {body′ = body} found =
  subst (λ closed → Scoped 0 closed) (just-inj found) sc-atom_type
alias-ind : IndEnv
alias-ind = record { families = [] ; builtins = λ _ → nothing }
module AliasModel = Reduction.Model alias-sig
  (λ {f} {body′} → alias-closed {f = f} {body′ = body′})
module Alias = Derive alias-ind alias-sig AliasModel.conversion AliasModel.reduce-converts

alias-leaf : Alias.N._⊢_⇒_ ⟨⟩ (tm-global "Alias#atom") (tm-type l0)
alias-leaf = require (Alias.at ⟨⟩ (tm-global "Alias#atom") (tm-type l0) r-leaf) refl
alias-unfolds : Conversion._≈_ AliasModel.conversion tm-atom_type (tm-global "Alias#atom")
alias-unfolds = require
  (Alias.conversion tm-atom_type (tm-global "Alias#atom") (c-sym (c-delta "Alias#atom"))) refl
alias-goal-replayed : Alias.N._⊢_⇒_ ⟨⟩ (tm-atom_lit "v") (tm-global "Alias#atom")
alias-goal-replayed = require
  (Alias.at ⟨⟩ (tm-atom_lit "v") (tm-global "Alias#atom")
    (r-convert (tm-global "Alias#atom") (c-sym (c-delta "Alias#atom")) r-leaf)) refl

-- Kind discovery THROUGH conversion: the declared type of `Alias#kind` is
-- a β-REDEX, so its sort is only visible after the conversion is replayed.
-- The asserted sort is recipe data and is justified by the recipe.
alias-kind-replayed : ∃ λ level → Alias.N._⊢_⇒_ ⟨⟩ (tm-global "Alias#kind") (tm-type level)
alias-kind-replayed = require
  (Alias.kind ⟨⟩ (tm-global "Alias#kind") (r-convert (tm-type l0) c-beta r-leaf)) refl

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
module Box = Derive box-ind box-sig BoxConversion.conversion BoxConversion.reduce-converts
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
