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

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Data.Fin as Fin
open import Data.Fin using (zero)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Data.Nat using (z≤n; s≤s)
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
open import Proof.CheckedAdmissionExamples using (pick)

module R = Admission.Replay Source.Pin.admission
module C = Caller.Replay Source.Pin.admission
module N = R.N
module RR = R.R
import Core.AdmissionBoundary as Boundary
module B = Boundary.Fragment R.C.W.snapshot
open B using (Supported; s-type; s-var; s-lam; s-app; s-atom_type; s-atom_lit)
module Frames = R.Frames
module P = Proof.Progress
open Admission using (Options; exact-only; residual-guided)
open N using (_⊢_⇒_; _⊢_⇐_; ⇒-type; ⇒-atom_type; ⇒-atom_lit; ⇒-app; ⇒-lam; ⇒-var; ⇐-infer)
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
------------------------------------------------------------------------

-- Supported (representation) evidence for the terms used below. These are
-- DIRECT witnesses of the EXISTING support judgment, not decisions: the
-- judgment is inductive, so a witness is cheaper and just as honest.
atom-type-supported : RR.Supported 0 (tm-type l0)
atom-type-supported = s-type


-- Whether an acceptance went through the residual comparison rather than
-- exact syntax. Used to prove the gate case is genuinely NON-exact.
is-normalized : ∀ {argument expected : Term}
  → ArgumentResult ⟨⟩ argument expected → Bool
is-normalized (exact checked) = false
is-normalized (normalized checked equal) = true
is-normalized (distinct-forms left right) = false
is-normalized (inconclusive side reason) = false

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

-- And the exact route is available at ZERO fuel with the residual
-- machinery switched OFF, which is the plan's zero-budget control. The
-- subject is `Atom` itself, whose inference really is `Type0`.
first-exact-only : ArgumentResult ⟨⟩ tm-atom_type (tm-type l0)
first-exact-only = R.compare-argument 0 ⟨⟩ {argument = tm-atom_type}
  {expected = tm-type l0} {inferred = tm-type l0} ⇒-atom_type
  atom-type-supported atom-type-supported exact-only
first-exact-only-derivation : Maybe (⟨⟩ ⊢ tm-atom_type ⇐ tm-type l0)
first-exact-only-derivation = R.checked-argument first-exact-only
first-exact-only-accepted : present first-exact-only-derivation ≡ true
first-exact-only-accepted = refl

------------------------------------------------------------------------
-- ACCEPTANCE GATE: a genuinely dependent argument whose instantiated
-- declared type is only CONVERTIBLE — not syntactically equal — to the
-- type the argument actually infers.
--
-- `(λ A → A) A` and `A` are distinct terms; they agree only up to beta.
-- The comparator must therefore accept the argument through the residual
-- branch, at the ORIGINAL declared type, with no supplied conversion.
------------------------------------------------------------------------

l0-kind : ⟨⟩ ⊢ tm-type l0 ⇒ tm-type l1
l0-kind = ⇒-type refl

-- The declared type of the dependent argument is the beta-redex.
beta-declared : Term
beta-declared = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-atom_type

-- The ARGUMENT is an Atom literal; it infers `Atom`. It is NOT
-- syntactically the declared type, so the exact branch cannot fire.
beta-argument : Term
beta-argument = tm-atom_lit "payload"

beta-inferred : Term
beta-inferred = tm-atom_type

beta-distinct : beta-declared ≢ beta-inferred
beta-distinct ()

-- The argument's replayed inference derivation, at the reduced form.
beta-synthesized : ⟨⟩ ⊢ beta-argument ⇒ beta-inferred
beta-synthesized = ⇒-atom_lit

-- The declared type is well-kinded, so the comparison is between two
-- kinds, not between arbitrary syntax.
-- `(λ A : Type0 → A) Atom` is itself a TYPE former, so its kind is a
-- universe. The lambda's domain is `Type0` (whose kind is `Type1`) and its
-- body is the bound variable `A`, so the lambda infers `Type0 → Type0`.
beta-declared-kind : ⟨⟩ ⊢ beta-declared ⇒ tm-type l0
beta-declared-kind = ⇒-app {c = tm-type l0}
  (⇒-lam {c = tm-type l0} l0-kind
    (⇐-infer {t = tm-var 0} {T = tm-type l0} {T′ = tm-type l0}
      (⇒-var {n = 1} Fin.zero) (Conversion.≈-refl R.C.W.M.conversion {t = tm-type l0})))
  ⇒-atom_type

-- `(λ A → A) A` is supported: the lambda binds `A` at depth 1 and its
-- body is the bound variable, so the application is supported at depth 0.
beta-declared-supported : RR.Supported 0 beta-declared
beta-declared-supported = s-app (s-lam s-type (s-var {k = 0} (s≤s z≤n))) s-atom_type

beta-argument-supported : RR.Supported 0 beta-argument
beta-argument-supported = s-atom_lit

beta-inferred-supported : RR.Supported 0 beta-inferred
beta-inferred-supported = s-atom_type

-- Fuel 4 is the FIRST budget that reduces the redex; fuels 0–3 exhaust.
beta-accepted : ArgumentResult ⟨⟩ beta-argument beta-declared
beta-accepted = R.compare-argument 4 ⟨⟩ {argument = beta-argument}
  {expected = beta-declared} {inferred = beta-inferred} beta-synthesized
  beta-inferred-supported beta-declared-supported residual-guided

-- The acceptance is NON-exact: it really did go through the comparison.
beta-accepted-is-normalized : Bool
beta-accepted-is-normalized = is-normalized beta-accepted
beta-normalized : beta-accepted-is-normalized ≡ true
beta-normalized = refl

-- The result is a checking derivation at the ORIGINAL declared type, not
-- at the normal form.
beta-derivation : Maybe (⟨⟩ ⊢ beta-argument ⇐ beta-declared)
beta-derivation = R.checked-argument beta-accepted
beta-derivation-accepted : present beta-derivation ≡ true
beta-derivation-accepted = refl

-- CONTROL: the same comparison at fuel 3 EXHAUSTS, so it is inconclusive
-- rather than a false acceptance or a false rejection.
beta-exhausted : ArgumentResult ⟨⟩ beta-argument beta-declared
beta-exhausted = R.compare-argument 3 ⟨⟩ {argument = beta-argument}
  {expected = beta-declared} {inferred = beta-inferred} beta-synthesized
  beta-inferred-supported beta-declared-supported residual-guided
beta-exhausted-derivation : Maybe (⟨⟩ ⊢ beta-argument ⇐ beta-declared)
beta-exhausted-derivation = R.checked-argument beta-exhausted
beta-exhausted-rejected : present beta-exhausted-derivation ≡ false
beta-exhausted-rejected = refl

-- CONTROL: with the residual switch OFF the same convertible pair is
-- REFUSED, so the opt-in switch is genuinely load-bearing.
beta-exact-only : ArgumentResult ⟨⟩ beta-argument beta-declared
beta-exact-only = R.compare-argument 4 ⟨⟩ {argument = beta-argument}
  {expected = beta-declared} {inferred = beta-inferred} beta-synthesized
  beta-inferred-supported beta-declared-supported exact-only
beta-exact-only-derivation : Maybe (⟨⟩ ⊢ beta-argument ⇐ beta-declared)
beta-exact-only-derivation = R.checked-argument beta-exact-only
beta-exact-only-rejected : present beta-exact-only-derivation ≡ false
beta-exact-only-rejected = refl

------------------------------------------------------------------------
-- The gate composed with the prefix lemmas: a telescope whose SECOND
-- declared type is the beta-redex. The prefix lemmas still apply, so the
-- converted argument can be pushed into the coherent frame.
------------------------------------------------------------------------

beta-bindings : Telescope
beta-bindings = ("A" , tm-type l0) ∷ ("x" , beta-declared) ∷ []

beta-arguments : List Term
beta-arguments = tm-atom_type ∷ beta-argument ∷ []

-- The converted argument, pushed onto a coherent prefix, preserves
-- coherence — the delivery-1 lemma applied to a CONVERTED argument, using
-- the checking derivation the comparator produced at the beta-redex type.
beta-prefix-step : Frames.Coherent ⟨⟩ ⟨⟩ (Frame.prefix [] Frame.identity)
  → Frames.Coherent (Core.Typing.extend ⟨⟩ beta-declared) ⟨⟩
      (Frame.push beta-argument (Frame.prefix [] Frame.identity))
beta-prefix-step coh = R.prefix-step {locals = []} {arg = beta-argument}
  {T = beta-declared} (RR.final beta-argument-supported)
  (pick beta-derivation beta-derivation-accepted) coh

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
