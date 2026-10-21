{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Recipes are plain untrusted data. EVERY exported family, constructor
-- and global -- including the dependent case -- now replays, so the whole
-- finite certificate is assembled from recipes. Conversion recipes
-- certify β/ζ/δ and congruence steps, so β-converted goals (the branch
-- goals in particular) no longer fail on syntax alone.
-- No byte parser, Elixir producer or η/NbE refinement is claimed.
------------------------------------------------------------------------
module Proof.NativeRecipeExamples where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Coverage using (CaseCoverage; HasBranch; lookup-ctor-members)
import Core.LocalFrame as Frame
import Core.DependentTyping as NativeTyping
open import Core.Signature
open import Core.Reduction
import Data.Bool as Bool
open import Proof.Confluence using (ClosedBody)
import Proof.ReductionConversion as Reduction
open import Core.NativeRecipe
import Core.CanonicalSnapshot as S
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
-- The wrong packet still fails; the case needs its own recipe (below).
wrong-packet-for-case : present (G.replay Input.raw-unpack scalar-packet) ≡ false
wrong-packet-for-case = refl

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
  (λ ())

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
box-owner-visible : ∀ {name family ctor}
  → findCtor name (IndEnv.families box-ind) ≡ just (family , ctor)
  → findFamily (fam-name family) (IndEnv.families box-ind) ≡ just family
box-owner-visible {name} found
  with lookup-ctor-members {c = name} {fs = box-family ∷ []} found
... | here refl , rest = refl
... | there () , rest
module Box = Derive box-ind box-sig BoxConversion.conversion BoxConversion.reduce-converts
  (λ {name} {family} {ctor} found →
    box-owner-visible {name = name} {family = family} {ctor = ctor} found)
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

------------------------------------------------------------------------
-- REPLAYED FAMILY AND CONSTRUCTOR DECLARATIONS
--
-- The telescopes are the ACTUAL declaration; the recipes supply one kind
-- derivation per entry and the result spines. Scope, uniformity and field
-- universe bounds are checked by the replayer.
------------------------------------------------------------------------

pack-recipe alternate-recipe : ConstructorRecipe
pack-recipe = record
  { ctor-parameter-recipes = []
  ; ctor-field-recipes = r-leaf ∷ r-leaf ∷ []
  ; ctor-result-parameter-recipes = []
  ; ctor-result-index-recipes = r-leaf ∷ [] }
alternate-recipe = record
  { ctor-parameter-recipes = []
  ; ctor-field-recipes = r-leaf ∷ r-leaf ∷ []
  ; ctor-result-parameter-recipes = []
  ; ctor-result-index-recipes = r-app (r-lam r-leaf r-leaf) r-leaf ∷ [] }
fixture-recipes : List FamilyRecipe
fixture-recipes = record
  { fam-parameter-recipes = [] ; fam-index-recipes = r-leaf ∷ []
  ; fam-constructor-recipes = pack-recipe ∷ alternate-recipe ∷ [] } ∷ []

replayed-families : All.All G.C.FamilyEvidence (S.Snapshot.family-entries Input.snapshot)
replayed-families = require
  (G.family-table (S.Snapshot.family-entries Input.snapshot) fixture-recipes) refl
replayed-family : D.N.FamilyDeclaration E.family
replayed-family = G.C.FamilyEvidence.declaration (All.lookup replayed-families (here refl))
replayed-pack : D.N.ConstructorDeclaration E.family E.pack
replayed-pack = All.lookup
  (G.C.FamilyEvidence.constructors (All.lookup replayed-families (here refl))) (here refl)
replayed-alternate : D.N.ConstructorDeclaration E.family E.alternate
replayed-alternate = All.lookup
  (G.C.FamilyEvidence.constructors (All.lookup replayed-families (here refl)))
  (there (here refl))

-- A parameter-bearing declaration: `Box(A)` with a uniform result-parameter
-- vector and a dependent field type.
box-recipe : ConstructorRecipe
box-recipe = record
  { ctor-parameter-recipes = r-leaf ∷ []
  ; ctor-field-recipes = r-leaf ∷ []
  ; ctor-result-parameter-recipes = r-leaf ∷ []
  ; ctor-result-index-recipes = [] }
box-declaration : Box.N.ConstructorDeclaration box-family box-ctor
box-declaration = require (Box.constructor-declaration box-family box-ctor box-recipe) refl

------------------------------------------------------------------------
-- REPLAYED DEPENDENT CASE
--
-- The motive is the curried Π the native rule requires, at an ASSERTED
-- level; each branch body is checked at its `branchGoal` inside a branch
-- context rebuilt from per-field kind recipes; coverage is replayed by
-- enumerating the registered constructors.
------------------------------------------------------------------------

case-field-recipes : List Recipe
case-field-recipes = r-leaf ∷ r-leaf ∷ []
case-kind-recipe : Recipe
case-kind-recipe = r-pi r-leaf (r-pi (r-data [] (r-leaf ∷ [])) r-leaf)
case-motive-recipe : Recipe
case-motive-recipe = r-lam r-leaf (r-lam (r-data [] (r-leaf ∷ [])) r-leaf)

-- `Boundary#Pack` takes its index from the field `A`, so its branch goal is
-- the motive applied to `A` and the surface constructor: exactly two β
-- steps, through the interior redex's lam.
pack-middle : Term
pack-middle =
  tm-app
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 1 ∷ [])) (tm-var 2))
    (tm-ctor "Boundary#Pack" (tm-var 1 ∷ tm-var 0 ∷ []))
pack-conversion : ConvRecipe
pack-conversion = c-sym (c-trans pack-middle (c-app c-beta c-refl) c-beta)

-- `Boundary#Alternate` computes its index as `(λ A → A) A`, so the third β
-- step is needed after the two motive applications.
alternate-index : Term
alternate-index =
  tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) (tm-var 1)
alternate-middle : Term
alternate-middle =
  tm-app
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (alternate-index ∷ []))
      (tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) (tm-var 2)))
    (tm-ctor "Boundary#Alternate" (tm-var 1 ∷ tm-var 0 ∷ []))
alternate-conversion : ConvRecipe
alternate-conversion =
  c-sym (c-trans alternate-middle (c-app c-beta c-refl)
    (c-trans alternate-index c-beta c-beta))

unpack-case-branches : List (List Recipe × Recipe)
unpack-case-branches =
  (case-field-recipes ,
    r-convert (NativeTyping.branchGoal "Boundary#Pack" [] E.pack E.motive-term)
      pack-conversion r-leaf) ∷
  (case-field-recipes ,
    r-convert (NativeTyping.branchGoal "Boundary#Alternate" [] E.alternate E.motive-term)
      alternate-conversion r-leaf) ∷ []

unpack-case-recipe : Recipe
unpack-case-recipe =
  r-case (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])) [] (r-leaf ∷ []) l0
    case-kind-recipe case-motive-recipe unpack-case-branches

-- The whole case synthesizes the motive applied to the scrutinee's index and
-- value; the global's declared goal is the reduced sort inhabitant.
unpack-middle : Term
unpack-middle =
  tm-app
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])) tm-atom_type)
    (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ []))
unpack-conversion : ConvRecipe
unpack-conversion = c-trans unpack-middle (c-app c-beta c-refl) c-beta

unpack-packet : Packet
unpack-packet = packet r-leaf
  (just (r-convert tm-atom_type unpack-conversion unpack-case-recipe))

-- The case's synthesized type IS the curried motive application at the
-- scrutinee's index and value, so the global's assertion needs a real
-- conversion (below) rather than a claim.
case-inferred : Term
case-inferred = proj₁ (require (D.infer ⟨⟩ E.program unpack-case-recipe) refl)
case-inferred-agrees : case-inferred ≡
  NativeTyping.apps E.motive-term (tm-atom_type ∷ E.value ∷ [])
case-inferred-agrees = refl

-- Each branch body really is checked in a REBUILT branch context: scope
-- and field kinds are re-derived, and the body is checked at its
-- `branchGoal` (which is why each branch needs a conversion recipe).
branch-context : Ctx 2
branch-context = extend (extend ⟨⟩ (tm-type l0)) (tm-var 0)
replayed-opened : ∃ λ m → ∃ λ (Δ : Ctx m) → D.N.WellFormed Δ
  × NativeTyping.Opened ⟨⟩ (Frame.advance [] Frame.identity) (ctor-args E.pack) Δ
replayed-opened = require
  (D.opened-fields ⟨⟩ (Frame.advance [] Frame.identity) (ctor-args E.pack)
    case-field-recipes D.N.wf[]) refl
replayed-pack-body : D.N._⊢_⇐_ branch-context (tm-var 0)
  (NativeTyping.branchGoal "Boundary#Pack" [] E.pack E.motive-term)
replayed-pack-body = require
  (D.checking branch-context (tm-var 0)
    (NativeTyping.branchGoal "Boundary#Pack" [] E.pack E.motive-term)
    (r-convert (NativeTyping.branchGoal "Boundary#Pack" [] E.pack E.motive-term)
      pack-conversion r-leaf)) refl
replayed-branches : D.N.Branches ⟨⟩ E.family [] E.motive-term E.branches
replayed-branches = require
  (D.branches ⟨⟩ E.family "Boundary#Packed" [] E.motive-term E.branches
    unpack-case-branches Input.family-lookup D.N.wf[]) refl
replayed-coverage : CaseCoverage E.ind "Boundary#Packed" E.branches
replayed-coverage = require (coverage? E.ind "Boundary#Packed" E.branches) refl

-- The fourth global's raw body is a dependent case: it now replays.
unpack-evidence : G.C.GlobalEvidence Input.raw-unpack
unpack-evidence = require (G.replay Input.raw-unpack unpack-packet) refl

-- The COMPLETE exported certificate, with every family, constructor and
-- global (including the dependent case) produced by replay.
replayed-certificate : G.C.Evidence
replayed-certificate = require
  (G.certificate fixture-recipes
    (scalar-packet ∷ scalar-packet ∷ packed-packet ∷ unpack-packet ∷ [])) refl

-- The certificate used by the safety composition is the FULLY REPLAYED
-- one: no family, constructor or global proof object is supplied by hand.
replayed-evidence : G.C.Evidence
replayed-evidence = replayed-certificate
replayed-valid : E.N.SignatureValid
replayed-valid = G.C.validity replayed-evidence
replayed-program-admitted : E.N.Admitted ⟨⟩ E.program tm-atom_type
replayed-program-admitted = G.C.admitted replayed-evidence {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl
replayed-program-eligible : G.C.A.Eligible ⟨⟩ E.program tm-atom_type
replayed-program-eligible = G.C.eligible replayed-evidence {entry = Input.raw-unpack}
  (there (there (there (here refl)))) refl

specification : Safety.Specification E.ind E.sig E.conv
specification = record Existing.specification
  { signature-valid = replayed-valid
  ; reduction-converts = λ {t} {u} → Input.ConversionModel.reduce-converts {t = t} {u = u}
  ; global-bodies-final = λ {name} → Input.visible-bodies-final {name} }
module Sound = Safety.Sound E.ind E.sig E.conv specification
replayed-safe : Sound.SafeState (tm-atom_lit "payload") tm-atom_type
replayed-safe = Sound.trace-safe
  (G.C.A.Eligible.checked replayed-program-eligible)
  (G.C.A.Eligible.source-final replayed-program-eligible)
  (⇝*-step (ι refl refl) ⇝*-refl)
