{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Context evidence is derived from declarations/binders/branch fields.
-- The untrusted caller grammar and recipes carry no native proof fields.
------------------------------------------------------------------------
module Proof.CaseContextExamples where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l2)
open import Core.Typing using (⟨⟩; extend)
open import Core.NativeRecipe
open import Core.CheckedAdmission using (present)
open import Proof.CheckedAdmissionExamples using (pick; obtain; obtain-result)
import Core.CallerAdmission as Caller
import Core.WireCaller as Wire
import Core.Wire as W
import Core.ClosureQuote as Q
import Proof.ClosureQuotationExamples as Quotation
import Proof.ClosureQuotationSafety as Safety
import Proof.CallerAdmissionExamples as Previous
import Proof.NativeRecipeExamples as Recipes
import Proof.NativeCertificateExamples as Existing
import Proof.RecursiveCaseExamples as Recursive
import Proof.WireSnapshotExamples as Source
import Core.DependentTyping as Native
import Core.LocalFrame as Frame
open import Core.Signature using (ctor-args)
import Fixtures.ExecutableBundle as Bundle
import Fixtures.ExecutableCaseContext as Produced
import Fixtures.ExecutableRecursiveCase as Observed
module R = Previous.R
module Chars = Previous.Chars
module C = R.C
module D = R.D
module Safe = Safety.Safe Source.Pin.admission

case-program : Term → Term
case-program scrutinee = tm-case scrutinee Existing.motive-term Existing.branches
case-at : Term → Term → Term → Recipe
case-at goal index scrutinee = r-convert goal
  (c-trans (tm-app
    (tm-lam unrestricted (tm-data "Boundary#Packed" [] (index ∷ [])) (rename wk index)) scrutinee)
    (c-app c-beta c-refl) c-beta) Recipes.unpack-case-recipe
open-scrutinee : Term
open-scrutinee = tm-ctor "Boundary#Pack" (tm-var 1 ∷ tm-var 0 ∷ [])
open-case : Term
open-case = case-program open-scrutinee
open-recipe : Recipe
open-recipe = case-at (tm-var 1) (tm-var 1) open-scrutinee
dependent : Caller.Request
dependent = record Previous.dependent { subject = open-case ; subject-recipe = open-recipe }
lambda-scrutinee : Term
lambda-scrutinee = tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-var 0 ∷ [])
lambda : Caller.Request
lambda = Caller.request [] [] [] []
  (tm-lam unrestricted tm-atom_type (case-program lambda-scrutinee))
  (tm-pi unrestricted tm-atom_type tm-atom_type)
  (r-lam r-leaf (case-at tm-atom_type tm-atom_type lambda-scrutinee)) (r-pi r-leaf r-leaf)
nested : Caller.Request
nested = Caller.request [] [] [] []
  (tm-case Existing.value Existing.motive-term
    (("Boundary#Pack" , 2 , open-case) ∷ ("Boundary#Alternate" , 2 , open-case) ∷ []))
  tm-atom_type
  (r-convert tm-atom_type Recipes.unpack-conversion
    (r-case (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])) [] (r-leaf ∷ []) l0
      Recipes.case-kind-recipe Recipes.case-motive-recipe
      ((Recipes.case-field-recipes ,
          r-convert (Native.branchGoal "Boundary#Pack" [] Existing.pack Existing.motive-term)
            Recipes.pack-conversion open-recipe) ∷
       (Recipes.case-field-recipes ,
          r-convert (Native.branchGoal "Boundary#Alternate" [] Existing.alternate Existing.motive-term)
            Recipes.alternate-conversion open-recipe) ∷ []))) r-leaf

module Artifact (query : Caller.Request) (chars quoted-chars : List Char) (quoted : Term)
  (encoded : Wire.encode Bundle.table query ≡ just chars)
  (accepted : present (R.verify query) ≡ true)
  (quoted-decoded : W.decode-term Bundle.table quoted-chars ≡ just quoted)
  (normalized : Quotation.term-result
    (Q.normalise 64 0 (R.Checked.closed-subject (pick (R.verify query) accepted)) []) ≡ just quoted) where
  decoded : Wire.decode Bundle.table chars ≡ just query
  decoded = Wire.roundtrip Bundle.table query chars encoded
  wire-accepted : present (Chars.verify chars) ≡ true
  wire-accepted = trans (Chars.verify-decoded chars query decoded) accepted
  wire-checked : Chars.Checked chars
  wire-checked = obtain (Chars.verify chars) wire-accepted
  exact-wire-result : Chars.verify chars ≡ just wire-checked
  exact-wire-result = obtain-result (Chars.verify chars) wire-accepted
  wire-native : R.Checked query
  wire-native = Chars.pin wire-checked query decoded
  -- Use the direct data verifier for computation, not a transported
  -- proof projection; both results are independently indexed by query.
  checked : R.Checked query
  checked = pick (R.verify query) accepted
  execution : Q.Normalizes 0 [] (R.Checked.closed-subject checked) quoted
  execution = Quotation.extract (Q.normalise 64 0 (R.Checked.closed-subject checked) []) quoted normalized
  safe : C.Sound.SafeState quoted (R.Checked.closed-goal checked)
  safe = proj₂ (Safe.safe-normalization checked execution)
  budgets-agree : ∀ budget → R.Checked.run checked budget
    ≡ C.Sound.truncate budget (R.Checked.tree checked)
  budgets-agree = R.Checked.budgets-agree checked

module Dependent = Artifact dependent Produced.dependent-characters Produced.dependent-quoted-characters
  (tm-atom_lit "payload") refl refl refl refl
module Lambda = Artifact lambda Produced.lambda-characters Produced.lambda-quoted-characters
  (tm-lam unrestricted tm-atom_type (tm-var 0)) refl refl refl refl
module Nested = Artifact nested Produced.nested-characters Produced.nested-quoted-characters
  (tm-atom_lit "payload") refl refl refl refl
dependent-subject-closes : R.Checked.closed-subject Dependent.checked ≡ Existing.program
dependent-subject-closes = refl
dependent-goal-closes : R.Checked.closed-goal Dependent.checked ≡ tm-atom_type
dependent-goal-closes = refl
dependent-safe : C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
dependent-safe = Dependent.safe
lambda-safe : C.Sound.SafeState (tm-lam unrestricted tm-atom_type (tm-var 0))
  (tm-pi unrestricted tm-atom_type tm-atom_type)
lambda-safe = Lambda.safe
nested-safe : C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
nested-safe = Nested.safe

-- Raw lookup/length does not certify a context. Even a valid raw context
-- needs an explicit derived witness at this entry point.
raw-context-unverified : D.context? (extend ⟨⟩ tm-atom_type) ≡ nothing
raw-context-unverified = refl
raw-case-rejected : present (D.infer (extend ⟨⟩ tm-atom_type)
  Existing.program Recipes.unpack-case-recipe) ≡ false
raw-case-rejected = refl
missing-evidence-stays-missing : present (D.infer-in (extend ⟨⟩ tm-atom_type) nothing
  (Caller.Request.subject lambda) (Caller.Request.subject-recipe lambda)) ≡ false
missing-evidence-stays-missing = refl
checked-context-accepted : present (D.infer-wf (extend ⟨⟩ tm-atom_type)
  (R.N.wf∷ R.N.wf[] sc-atom_type R.N.⇒-atom_type) Existing.program Recipes.unpack-case-recipe) ≡ true
checked-context-accepted = refl
raw-variable-still-infers : present (D.infer (extend ⟨⟩ tm-atom_type) (tm-var 0) r-leaf) ≡ true
raw-variable-still-infers = refl
bad-domain-kind : present (R.verify (record lambda
  { subject = tm-lam unrestricted (tm-type l2) (case-program lambda-scrutinee) })) ≡ false
bad-domain-kind = refl
escaped-domain : present (R.verify (record lambda
  { subject = tm-lam unrestricted (tm-var 0) (case-program lambda-scrutinee) })) ≡ false
escaped-domain = refl
wrong-lambda-recipe : present (R.verify (record lambda
  { subject-recipe = r-lam (r-lam r-leaf r-leaf) (case-at tm-atom_type tm-atom_type lambda-scrutinee) })) ≡ false
wrong-lambda-recipe = refl
wrong-goal : present (R.verify (record dependent { goal = tm-float_type })) ≡ false
wrong-goal = refl
wrong-actual : present (R.verify (record dependent { arguments = tm-float_type ∷ tm-atom_lit "payload" ∷ [] })) ≡ false
wrong-actual = refl
missing-context-kind : present (R.verify (record dependent { kind-recipes = r-leaf ∷ [] })) ≡ false
missing-context-kind = refl
escaped-scrutinee : present (R.verify (record dependent
  { subject = case-program (tm-ctor "Boundary#Pack" (tm-var 2 ∷ tm-var 0 ∷ [])) })) ≡ false
escaped-scrutinee = refl
missing-coverage : present (R.verify (record dependent
  { subject = tm-case open-scrutinee Existing.motive-term (("Boundary#Pack" , 2 , tm-var 0) ∷ []) })) ≡ false
missing-coverage = refl
wrong-first-field-count : present (R.verify (record dependent
  { subject = tm-case open-scrutinee Existing.motive-term
      (("Boundary#Pack" , 1 , tm-var 0) ∷ ("Boundary#Alternate" , 2 , tm-var 0) ∷ []) })) ≡ false
wrong-first-field-count = refl
short-branch-kind-vector : present (D.opened-fields
  (R.Checked.context Dependent.checked) (Frame.advance [] Frame.identity) (ctor-args Existing.pack)
  (r-leaf ∷ []) (R.Checked.context-valid Dependent.checked)) ≡ false
short-branch-kind-vector = refl
non-kind-branch-field : present (D.opened-fields
  (R.Checked.context Dependent.checked) (Frame.advance [] Frame.identity) (ctor-args Existing.pack)
  (r-lam r-leaf r-leaf ∷ r-leaf ∷ []) (R.Checked.context-valid Dependent.checked)) ≡ false
non-kind-branch-field = refl
-- Forward declaration replay also retains checked prior entry kinds.
case-in-forward-telescope : present (D.declare ⟨⟩
  (("x" , tm-atom_type) ∷ ("A" , Observed.type-program) ∷ [])
  (r-leaf ∷ Recursive.type-kind ∷ [])) ≡ true
case-in-forward-telescope = refl
caller-goal-kind-uses-context : present (D.kind-wf
  (R.Checked.context Dependent.checked) (R.Checked.context-valid Dependent.checked)
  Observed.type-program Recursive.type-kind) ≡ true
caller-goal-kind-uses-context = refl
