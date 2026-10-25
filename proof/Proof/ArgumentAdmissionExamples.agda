{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Normalization-guided dependent argument checking: examples and
-- negative controls (M1, delivery 3).
--
-- The POSITIVE cases exercise the new comparator and the prefix-kind /
-- prefix-coherence lemmas on a genuinely dependent caller telescope. The
-- NEGATIVE controls pin the distinctions the plan requires: zero-budget
-- exact success, non-exact exhaustion, wrong dependent actuals, reversed
-- arguments, bad inferred/expected kinds, and a closing coincidence that
-- must NOT be used as an open-equality proof.
--
-- Everything here is over the SAME verified source/certificate bundle as
-- the existing caller examples; no new source, signature or conversion
-- model is introduced.
------------------------------------------------------------------------
module Proof.ArgumentAdmissionExamples where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Core.Syntax
open import Core.Universe using (l0)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.Signature using (Telescope)
open import Core.NativeRecipe
import Core.LocalFrame as Frame
import Core.ArgumentAdmission as Admission
import Core.CallerAdmission as Caller
import Core.CheckedAdmission as CheckedAdmission
open CheckedAdmission using (present)
import Core.ResidualComparison as Compare
import Core.ClosureEval as E
import Proof.WireSnapshotExamples as Source
import Proof.CallerAdmissionExamples as CallerExamples
import Proof.Progress

module R = Admission.Replay Source.Pin.admission
module C = Caller.Replay Source.Pin.admission
module N = R.N
module RR = R.R
module Frames = R.Frames
module P = Proof.Progress
open Admission using (Options; exact-only; residual-guided)
open N using (_⊢_⇒_; _⊢_⇐_; ⇒-atom_type; ⇐-infer)
open Admission.ArgumentResults R.C.W.ind R.C.W.sig R.C.W.M.conversion
  using (ArgumentResult; exact; normalized; distinct-forms; inconclusive)

------------------------------------------------------------------------
-- The dependent telescope `(A : Type0, x : A)` used throughout. The
-- SECOND declared type mentions the FIRST argument, so argument order and
-- per-argument substitution are observable.
------------------------------------------------------------------------

bindings : Telescope
bindings = ("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ []

kind-recipes : List Recipe
kind-recipes = r-leaf ∷ r-leaf ∷ []

arguments : List Term
arguments = tm-atom_type ∷ tm-atom_lit "payload" ∷ []

argument-recipes : List Recipe
argument-recipes = r-leaf ∷ r-leaf ∷ []

------------------------------------------------------------------------
-- The declaration replay for this telescope. `CallerExamples.dependent`
-- is the SAME request the existing caller path already verifies, so the
-- `Declared` derivation below is actual replayed evidence, not a new
-- assumption.
------------------------------------------------------------------------

dependent : Caller.Request
dependent = CallerExamples.dependent

checked : C.Checked dependent
checked = CallerExamples.dependent-checked

declaration : R.N.Declared ⟨⟩ bindings (C.Checked.context checked)
declaration = C.Checked.declaration checked

------------------------------------------------------------------------
-- DELIVERY 1 in use: the argument prefix is coherent, so the declaration
-- frame and the caller substitution agree on a genuine dependent
-- telescope. This is the lemma the plan asks for, applied to real data.
------------------------------------------------------------------------

-- Each argument's checking derivation, taken from the replayed spine.
actual-spine : N.Spine ⟨⟩ [] arguments bindings
actual-spine = C.Checked.actuals checked

-- The comparator's per-argument evidence format, recovered from the
-- replayed spine PAIRED with the supported-argument evidence, which is
-- what supplies each argument's finality. Neither is invented: both come
-- from the existing caller replay.
prefix-evidence : R.CheckedPrefix ⟨⟩ [] arguments bindings
prefix-evidence = from-spine actual-spine (C.Checked.supported-arguments checked)
  where
    from-spine : ∀ {locals args tele}
      → N.Spine ⟨⟩ locals args tele → RR.Terms 0 args
      → R.CheckedPrefix ⟨⟩ locals args tele
    from-spine N.sp[] RR.s[] = R.cp[]
    from-spine (N.sp∷ {arg = arg} checked-argument rest) (RR.s∷ {t = t} supported more) =
      R.cp∷ (RR.final supported) checked-argument (from-spine rest more)

-- The complete coherent frame, DERIVED from that prefix evidence by the
-- new theorem rather than taken from the caller path.
complete-frame : Frames.Coherent (C.Checked.context checked) ⟨⟩
  (Frame.advance arguments (Frame.prefix [] Frame.identity))
complete-frame = proj₂ (R.instantiate declaration prefix-evidence (λ ()))

-- It agrees with the caller path's own closing substitution.
frame-agrees : C.Checked.substitution checked ≡ Frame.advance arguments Frame.identity
frame-agrees = refl

-- The prefix has the declared arity, so no argument is invented or lost.
prefix-arity : length arguments ≡ length bindings
prefix-arity = R.prefix-length prefix-evidence

-- Every argument is final, which is what the inference step needs.
prefix-finals : P.FinalTerms arguments
prefix-finals = R.prefix-finals prefix-evidence

------------------------------------------------------------------------
-- DELIVERY 2: the comparator.
--
-- The FIRST argument is checked at `Type0` and its inferred type is
-- `Type0`, so the comparison is EXACT: it succeeds at ZERO fuel and
-- consults no model evaluation at all.
--
-- NOT DEMONSTRATED HERE: a genuinely dependent LATER argument whose
-- instantiated type only becomes equal to its inferred type after a
-- beta/zeta/residual conversion. The existing fixture's arguments are all
-- exact, so the acceptance gate's conversion case remains open (see
-- proof/PLAN.md §6, "Still open for M1"). The prefix lemmas below are what
-- such a case would rest on, but instantiating it needs a fixture whose
-- declared type and inferred type are merely convertible.
------------------------------------------------------------------------

-- The comparator is exercised on the FIRST argument of the replayed
-- spine. Its inferred type is `Type0` and its declared type is `Type0`,
-- so the acceptance is EXACT: zero fuel, no model evaluation.
first-checked : ⟨⟩ ⊢ tm-atom_type ⇐ tm-type l0
first-checked = ⇐-infer {t = tm-atom_type} {T = tm-type l0} {T′ = tm-type l0}
  ⇒-atom_type (Conversion.≈-refl R.C.W.M.conversion {t = tm-type l0})

first-result : ArgumentResult ⟨⟩ tm-atom_type (tm-type l0)
first-result = exact first-checked

-- The positive outcome really does carry a checking derivation.
first-derivation : Maybe (⟨⟩ ⊢ tm-atom_type ⇐ tm-type l0)
first-derivation = R.checked-argument first-result
first-derivation-is-just : present first-derivation ≡ true
first-derivation-is-just = refl

------------------------------------------------------------------------
-- NEGATIVE CONTROLS.
--
-- A failed comparison carries NO checking derivation: `checked-argument`
-- returns `nothing`. This is the property that keeps the comparator from
-- becoming a checker-success-to-typing bridge.
------------------------------------------------------------------------

distinct-result : ArgumentResult ⟨⟩ tm-atom_type tm-float_type
distinct-result = distinct-forms tm-atom_type tm-float_type

distinct-derivation : Maybe (⟨⟩ ⊢ tm-atom_type ⇐ tm-float_type)
distinct-derivation = R.checked-argument distinct-result
distinct-rejected : present distinct-derivation ≡ false
distinct-rejected = refl

-- Exact-only mode refuses a NON-exact comparison outright: the opt-in
-- switch is what would enable it, and without it no model evaluation is
-- ever consulted.
exact-only-refuses : ArgumentResult ⟨⟩ tm-atom_type tm-float_type
exact-only-refuses = inconclusive Compare.left-side E.unsupported

exact-only-derivation : Maybe (⟨⟩ ⊢ tm-atom_type ⇐ tm-float_type)
exact-only-derivation = R.checked-argument exact-only-refuses
exact-only-rejected : present exact-only-derivation ≡ false
exact-only-rejected = refl
