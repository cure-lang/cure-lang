{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Checked layout, scoped data-head readback and native typing are separate.
-- This fixture has BOTH a parameter and a dependent index.
------------------------------------------------------------------------
module Proof.DataSpineExamples where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Core.Syntax
open import Core.Universe using (l0; l1)
open import Core.Grade using (unrestricted)
open import Core.NativeRecipe
open import Core.Signature using (Family; findFamily; IndEnv; just-inj; nothing≠just)
open import Core.Typing using (⟨⟩)
open import Core.Reduction using (_⇝_; _⇝*_)
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller
import Core.DataSpine as Layout
import Core.DataReadback as Read
import Core.ClosureEval as E
import Core.ClosureScope as Scope
import Proof.DataReadback as Model
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quote
import Proof.CheckedAdmissionExamples as Pick
import Fixtures.ExecutableDataSpine as Observed

checked-source : Admission.Checked Observed.source Observed.table Observed.certificate-characters
checked-source = Pick.obtain (Admission.verify Observed.source Observed.table Observed.certificate-characters) refl
module C = Admission.Checked checked-source
module R = Caller.Replay checked-source
module D = R.D
module Simulation = Model.Simulation C.W.sig
module Safe = Model.Safe checked-source
family : Family
family = Pick.pick (findFamily "Spine#Indexed" (IndEnv.families C.W.ind)) refl
family-found : findFamily "Spine#Indexed" (IndEnv.families C.W.ind) ≡ just family
family-found = Pick.pick-equation (findFamily "Spine#Indexed" (IndEnv.families C.W.ind)) refl

present : ∀ {A} → Read.Result A → Bool
present (Read.done out) = true
present (Read.stop reason) = false
choose : ∀ {A} (result : Read.Result A) → present result ≡ true → A
choose (Read.done out) successful = out
choose (Read.stop reason) ()
module Case (depth : ℕ) (values : List E.Value) (quoted : Term)
  (successful : present (Read.run 64 depth C.W.ind "Spine#Indexed" values) ≡ true)
  (equal : Read.Output.term (choose (Read.run 64 depth C.W.ind "Spine#Indexed" values) successful) ≡ quoted) where
  output : Read.Output depth C.W.ind "Spine#Indexed" values
  output = choose (Read.run 64 depth C.W.ind "Spine#Indexed" values) successful
  scoped : Scoped depth quoted
  scoped = subst (Scoped depth) equal (Read.Output.scoped output)

module CanonicalCase = Case 0 Observed.canonical-flat Observed.canonical-quoted refl refl
module Redex = Case 0 Observed.redex-flat Observed.redex-quoted refl refl
module Parameter = Case 0 Observed.parameter-flat Observed.parameter-quoted refl refl
module Closure = Case 0 Observed.closure-flat Observed.closure-quoted refl refl
module Open = Case 1 Observed.open-flat Observed.open-quoted refl refl

parameters : Term → List Term
parameters (tm-data name ps is) = ps
parameters other = []
indices : Term → List Term
indices (tm-data name ps is) = is
indices other = []
spine-result : ∀ {A : List E.Value → Set} → E.Result (Σ (List E.Value) A) → Maybe (List E.Value)
spine-result (E.stop reason) = nothing
spine-result (E.done (values , proof)) = just values
spine-evidence : (args : List Term) (env values : List E.Value)
  → spine-result (E.run-spine 32 args env) ≡ just values → E.EvaluatesSpine env args values
spine-evidence args env values found with E.run-spine 32 args env
... | E.stop reason = ⊥-elim (nothing≠just found)
... | E.done (actual , proof) with just-inj found
... | refl = proof
ps-values : ∀ {d ind name values} → Read.Output d ind name values → List E.Value
ps-values out = Layout.Alignment.parameters (Read.Output.alignment out)
is-values : ∀ {d ind name values} → Read.Output d ind name values → List E.Value
is-values out = Layout.Alignment.indices (Read.Output.alignment out)
flat-scope : Scope.EnvironmentScoped 0 Observed.canonical-flat
flat-scope = Scope.s∷ Scope.s-atom-type (Scope.s∷ Scope.s-atom Scope.s[])

canonical-path : _⇝*_ C.W.sig Observed.canonical-program Observed.canonical-quoted
canonical-path = Simulation.normalization CanonicalCase.output flat-scope Meaning.d[]
  (spine-evidence (parameters Observed.canonical-program) [] (ps-values CanonicalCase.output) refl)
  (spine-evidence (indices Observed.canonical-program) [] (is-values CanonicalCase.output) refl)
redex-path : _⇝*_ C.W.sig Observed.redex-program Observed.redex-quoted
redex-path = Simulation.normalization Redex.output flat-scope Meaning.d[]
  (spine-evidence (parameters Observed.redex-program) [] (ps-values Redex.output) refl)
  (spine-evidence (indices Observed.redex-program) [] (is-values Redex.output) refl)
parameter-path : _⇝*_ C.W.sig Observed.parameter-program Observed.parameter-quoted
parameter-path = Simulation.normalization Parameter.output flat-scope Meaning.d[]
  (spine-evidence (parameters Observed.parameter-program) [] (ps-values Parameter.output) refl)
  (spine-evidence (indices Observed.parameter-program) [] (is-values Parameter.output) refl)
closure-scope : Scope.EnvironmentScoped 0 Observed.closure-flat
closure-scope = Scope.s∷ (Scope.s-pi Scope.s-atom-type Scope.s[] sc-atom_type)
  (Scope.s∷ (Scope.s-lam Scope.s-atom-type Scope.s[]
    (sc-app (sc-lam sc-atom_type (sc-var (s≤s z≤n))) (sc-var (s≤s z≤n)))) Scope.s[])
closure-path : _⇝*_ C.W.sig Observed.closure-program Observed.closure-quoted
closure-path = Simulation.normalization Closure.output closure-scope Meaning.d[]
  (spine-evidence (parameters Observed.closure-program) [] (ps-values Closure.output) refl)
  (spine-evidence (indices Observed.closure-program) [] (is-values Closure.output) refl)
open-path : _⇝*_ C.W.sig Observed.open-program Observed.open-quoted
open-path = Simulation.normalization Open.output
  (Scope.s∷ Scope.s-atom-type (Scope.s∷ (Scope.s-neutral (Scope.s-var (s≤s z≤n))) Scope.s[]))
  (Meaning.d∷ (Meaning.d-neutral (Meaning.d-var (s≤s z≤n))) Meaning.d[])
  (spine-evidence (parameters Observed.open-program) (E.v-neutral (E.n-var 0) ∷ []) (ps-values Open.output) refl)
  (spine-evidence (indices Observed.open-program) (E.v-neutral (E.n-var 0) ∷ []) (is-values Open.output) refl)
no-delta-irreducible : ∀ {endpoint} → _⇝_ Quote.no-delta Observed.closure-quoted endpoint → ⊥
no-delta-irreducible = Model.no-delta-step Closure.output

module Native (program : Term) (recipe : Recipe)
  (accepted : Admission.present (R.verify (Caller.request [] [] [] [] program (tm-type l1) recipe r-leaf)) ≡ true) where
  admitted : R.Checked (Caller.request [] [] [] [] program (tm-type l1) recipe r-leaf)
  admitted = Pick.pick (R.verify (Caller.request [] [] [] [] program (tm-type l1) recipe r-leaf)) accepted
  safe : ∀ {endpoint} → _⇝*_ C.W.sig (R.Checked.closed-subject admitted) endpoint
    → C.Sound.SafeState endpoint (R.Checked.closed-goal admitted)
  safe = R.Checked.trace-safe admitted
module CanonicalNative = Native Observed.canonical-program (r-data (r-leaf ∷ []) (r-leaf ∷ [])) refl
module RedexNative = Native Observed.redex-program
  (r-data (r-leaf ∷ []) (r-let r-leaf (r-app (r-lam r-leaf r-leaf) r-leaf) r-leaf ∷ [])) refl
module ParameterNative = Native Observed.parameter-program
  (r-data (r-app (r-lam r-leaf r-leaf) r-leaf ∷ [])
    (r-convert (tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-atom_type)
      (c-sym c-beta) r-leaf ∷ [])) refl
module ClosureNative = Native Observed.closure-program
  (r-data (r-pi r-leaf r-leaf ∷ []) (r-lam r-leaf (r-app (r-lam r-leaf r-leaf) r-leaf) ∷ [])) refl
canonical-safe : C.Sound.SafeState Observed.canonical-quoted (tm-type l1)
canonical-safe = CanonicalNative.safe canonical-path
redex-safe : C.Sound.SafeState Observed.redex-quoted (tm-type l1)
redex-safe = Safe.safe-readback RedexNative.admitted Redex.output refl flat-scope
  (spine-evidence (parameters Observed.redex-program) [] (ps-values Redex.output) refl)
  (spine-evidence (indices Observed.redex-program) [] (is-values Redex.output) refl)
parameter-safe : C.Sound.SafeState Observed.parameter-quoted (tm-type l1)
parameter-safe = ParameterNative.safe parameter-path
closure-safe : C.Sound.SafeState Observed.closure-quoted (tm-type l1)
closure-safe = ClosureNative.safe closure-path

canonical-split : Layout.split (Layout.signature C.W.ind) "Spine#Indexed"
  (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) ≡
  (tm-atom_type ∷ [] , tm-atom_lit "payload" ∷ [])
canonical-split = Layout.canonical C.W.ind "Spine#Indexed" family family-found _ _ refl
rebuild : Name → (List Term × List Term) → Term
rebuild name (ps , is) = tm-data name ps is
signature-free-agrees : rebuild "Spine#Indexed" (Layout.split Layout.signature-free "Spine#Indexed"
  (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])) ≡ Observed.canonical-fallback
signature-free-agrees = refl
unknown-model-agrees : rebuild "Spine#Unknown" (Layout.split (Layout.signature C.W.ind) "Spine#Unknown"
  (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])) ≡ Observed.unknown-quoted
unknown-model-agrees = refl
short-ordinary-split-agrees : rebuild "Spine#Indexed"
  (Layout.split (Layout.signature C.W.ind) "Spine#Indexed" (tm-atom_type ∷ [])) ≡ Observed.short-quoted
short-ordinary-split-agrees = refl
extra-ordinary-split-agrees : rebuild "Spine#Indexed"
  (Layout.split (Layout.signature C.W.ind) "Spine#Indexed"
    (tm-atom_type ∷ tm-atom_lit "payload" ∷ tm-atom_lit "payload" ∷ [])) ≡ Observed.extra-quoted
extra-ordinary-split-agrees = refl
fallback-differs : Observed.canonical-fallback ≢ Observed.canonical-quoted
fallback-differs ()
forged-source-split-changes : Observed.forged-program ≢ Observed.forged-quoted
forged-source-split-changes ()
forged-values-same : Observed.forged-flat ≡ Observed.canonical-flat
forged-values-same = refl
forged-native-kind-rejected : Admission.present (D.kind ⟨⟩ Observed.forged-program
  (r-data [] (r-leaf ∷ r-leaf ∷ []))) ≡ false
forged-native-kind-rejected = refl
ill-typed-layout-passes : present (Read.run 64 0 C.W.ind "Spine#Indexed" Observed.ill-typed-flat) ≡ true
ill-typed-layout-passes = refl
ill-typed-native-kind-rejected : Admission.present
  (D.kind ⟨⟩ Observed.ill-typed-program (r-data (r-leaf ∷ []) (r-leaf ∷ []))) ≡ false
ill-typed-native-kind-rejected = refl

failure : ∀ {A} → Read.Result A → Maybe Read.Failure
failure (Read.done out) = nothing
failure (Read.stop reason) = just reason
short-spine : failure (Read.run 64 0 C.W.ind "Spine#Indexed" Observed.short-flat)
  ≡ just (Read.layout-failure Layout.wrong-index-arity)
short-spine = refl
missing-parameters : failure (Read.run 64 0 C.W.ind "Spine#Indexed" [])
  ≡ just (Read.layout-failure Layout.missing-parameters)
missing-parameters = refl
extra-spine : failure (Read.run 64 0 C.W.ind "Spine#Indexed" Observed.extra-flat)
  ≡ just (Read.layout-failure Layout.wrong-index-arity)
extra-spine = refl
unknown-family : failure (Read.run 64 0 C.W.ind "Spine#Unknown" Observed.unknown-flat)
  ≡ just (Read.layout-failure Layout.unknown-family)
unknown-family = refl
unknown-fallback : Observed.unknown-quoted ≡ Observed.unknown-fallback
unknown-fallback = refl
small-budget : failure (Read.run 0 0 C.W.ind "Spine#Indexed" Observed.canonical-flat) ≡ just Read.exhausted
small-budget = refl
field-budget : failure (Read.run 1 0 C.W.ind "Spine#Indexed" Observed.canonical-flat)
  ≡ just (Read.field-failure E.exhausted)
field-budget = refl
escaped-field : failure (Read.run 64 0 C.W.ind "Spine#Indexed" Observed.open-flat)
  ≡ just (Read.field-failure E.escaped-level)
escaped-field = refl
shared-evaluation-still-excludes-data : E.run 64 Observed.canonical-program [] ≡ E.stop E.unsupported
shared-evaluation-still-excludes-data = refl
