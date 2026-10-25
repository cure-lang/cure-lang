{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Normalization-guided dependent argument checking (M1, deliveries 1-2).
--
-- The existing caller path (`Core.CallerAdmission`) checks every actual
-- argument by EXACT syntax against its instantiated declared type. This
-- module adds a SEPARATE, opt-in argument comparator that additionally
-- accepts a bounded residual comparison, and proves the prefix-kind and
-- coherence lemmas that make per-argument checking sound in the first
-- place.
--
-- PROVED here (no new postulate, no callback, no checker-success-to-typing
-- bridge):
--
--   * `prefix-step`: one declared entry plus one CHECKED actual argument
--     preserves native coherence of the declaration substitution.
--   * `prefix-coherent`: a typed prefix of actual arguments therefore
--     yields a native `Coherent` substitution into the declaration
--     context, for ARBITRARY telescopes. The next declared type, after
--     substituting the prefix only, is exactly the goal the next argument
--     is checked against; later arguments are never substituted into
--     earlier declaration types.
--   * `prefix-kind`: that instantiated next type is itself well-kinded in
--     the caller context, so no caller supplies an argument's expected
--     kind as an untrusted field.
--   * `instantiate`: the existing exact `Spine` judgment and the
--     coherent complete frame are DERIVED from the comparator's evidence.
--
-- NOT claimed: the comparator is not complete native typing, and a failed
-- comparison is not a non-conversion theorem. `distinct-forms` reports
-- only that two bounded executions produced distinct forms.
------------------------------------------------------------------------
module Core.ArgumentAdmission where

open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂)
open import Core.Syntax
open import Core.Signature using (Telescope; IndEnv)
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Universe using (Level)
open import Core.NativeRecipe using (Recipe)
import Core.CheckedAdmission as Admission
import Core.LocalFrame as F
import Core.DependentTyping as Native
import Proof.DependentCoherence as Coherence
import Proof.DependentGeneralTransport as General
import Proof.DependentScoping as Scope
import Proof.Progress as Final
import Core.ResidualComparison as Compare
import Proof.FreshEnvironment as Fresh
import Core.AmbientResidualAdmission as Ambient
import Core.SyntaxEquality as Syntax
import Proof.ResidualConversion as EqualityProof
import Proof.ClosureEvaluation as Meaning
import Core.ClosureEval as E

------------------------------------------------------------------------
-- The OPT-IN switch. It is the ONLY extra input relative to the existing
-- caller request: no expected kind, no conversion witness and no
-- comparison oracle becomes an untrusted field.
------------------------------------------------------------------------

record Options : Set where
  constructor options
  field
    residual : Bool
open Options public

exact-only : Options
exact-only = options false

residual-guided : Options
residual-guided = options true

------------------------------------------------------------------------
-- Per-argument comparison outcomes. Every POSITIVE outcome carries the
-- native checking derivation at the ORIGINAL instantiated expected type;
-- a normal form is never substituted for the caller's specification.
------------------------------------------------------------------------

module ArgumentResults (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv

  data ArgumentResult {n} (Γ : Ctx n) (argument expected : Term) : Set where
    exact : Γ ⊢ argument ⇐ expected → ArgumentResult Γ argument expected
    -- A NON-exact acceptance records the comparison that justified it: the
    -- argument's INFERRED TYPE against the declared expected type. The
    -- checking derivation itself is at the ORIGINAL expected type.
    normalized : ∀ {inferred : Term}
      → Γ ⊢ argument ⇐ expected
      → Compare.EqualResidual n (Fresh.environment n) inferred expected
      → ArgumentResult Γ argument expected
    distinct-forms : Term → Term → ArgumentResult Γ argument expected
    inconclusive : Compare.Side → E.Failure → ArgumentResult Γ argument expected

module Replay {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module C = Admission.Checked source-checked
  module N = C.W.N
  module D = C.W.G.D
  module R = C.W.R.R
  module Frames = Coherence.NativeFrames C.W.ind C.W.sig C.W.M.conversion
  module Transport = General.General C.W.ind C.W.sig C.W.M.conversion
  module T = Transport.Valid C.valid
  module Sc = Scope.Scoping C.W.ind C.W.sig C.W.M.conversion
  open Native.Typing C.W.ind C.W.sig C.W.M.conversion
  open ArgumentResults C.W.ind C.W.sig C.W.M.conversion

  ----------------------------------------------------------------------
  -- DELIVERY 1: prefix-kind and prefix-coherence.
  --
  -- `CheckedPrefix` is exactly the per-argument evidence a comparator
  -- produces: for every consumed argument, a native checking derivation
  -- at the type obtained by substituting the PRECEDING arguments only,
  -- plus the finality the inference step needs. Coherence is never
  -- inferred from list lengths.
  ----------------------------------------------------------------------

  data CheckedPrefix {n} (Γ : Ctx n) (locals : List Term) : List Term → Telescope → Set where
    cp[] : CheckedPrefix Γ locals [] []
    cp∷ : ∀ {arg args name T tele}
      → Final.Final arg
      → Γ ⊢ arg ⇐ F.instantiatePrefix locals T
      → CheckedPrefix Γ (arg ∷ locals) args tele
      → CheckedPrefix Γ locals (arg ∷ args) ((name , T) ∷ tele)

  prefix-length : ∀ {n} {Γ : Ctx n} {locals args tele}
    → CheckedPrefix Γ locals args tele → length args ≡ length tele
  prefix-length cp[] = refl
  prefix-length (cp∷ final checked rest) = cong suc (prefix-length rest)

  prefix-finals : ∀ {n} {Γ : Ctx n} {locals args tele}
    → CheckedPrefix Γ locals args tele → Final.FinalTerms args
  prefix-finals cp[] = Final.ft[]
  prefix-finals (cp∷ final checked rest) = Final.ft∷ final (prefix-finals rest)

  -- The declaration frame and the coherent substitution agree. This is the
  -- existing `F.prefix-args` law; the two directions are kept separate so
  -- that `subst` never has to unfold `instantiatePrefix` itself.
  prefix-equal : ∀ locals T
    → substS (F.prefix locals F.identity) T ≡ F.instantiatePrefix locals T
  prefix-equal locals T = cong (λ σ → substS σ T) (funext (F.prefix-args 0 locals))

  prefix-equal′ : ∀ locals T
    → F.instantiatePrefix locals T ≡ substS (F.prefix locals F.identity) T
  prefix-equal′ locals T = sym (prefix-equal locals T)

  -- ONE declared entry plus ONE checked actual argument preserves native
  -- coherence. The step consumes the actual native checking derivation
  -- and its finality; it never consumes a proof of its own conclusion.
  prefix-step : ∀ {n d} {Γ : Ctx n} {Δ : Ctx d} {locals arg T}
    → Final.Final arg
    → Γ ⊢ arg ⇐ F.instantiatePrefix locals T
    → Frames.Coherent Δ Γ (F.prefix locals F.identity)
    → Frames.Coherent (extend Δ T) Γ (F.push arg (F.prefix locals F.identity))
  prefix-step {Γ = Γ} {locals = locals} {arg = arg} {T = T} final checked coh =
    Frames.push-coherent coh
      (subst (λ A → Γ ⊢ arg ⇒ A) (prefix-equal′ locals T)
        (Frames.check-infer final checked))

  prefix-coherent : ∀ {n d e} {Γ : Ctx n} {Δ : Ctx d} {Ε : Ctx e}
    {locals args tele}
    → N.Declared Δ tele Ε
    → CheckedPrefix Γ locals args tele
    → Frames.Coherent Δ Γ (F.prefix locals F.identity)
    → Frames.Coherent Ε Γ (F.advance args (F.prefix locals F.identity))
  prefix-coherent N.dt[] cp[] coh = coh
  prefix-coherent {locals = locals} (N.dt∷ {T = T} scoped kind rest)
    (cp∷ {arg = arg} final checked prefix) coh =
    prefix-coherent rest prefix (prefix-step {locals = locals} {arg = arg} {T = T} final checked coh)

  -- The instantiated NEXT declared type is well-kinded in the caller
  -- context once the prefix is coherent, so callers never supply an
  -- argument's expected kind as an untrusted field.
  -- `subst⇒` takes the SUBSTITUTED context first: `Coherent Γ Δ σ` already
  -- relates the source context to its image.
  kind-transported : ∀ {n d} {Γ : Ctx n} {Δ : Ctx d} {σ : Sub} (T : Term) (l : Level)
    → Γ ⊢ T ⇒ tm-type l → WellFormed Δ → Frames.Coherent Γ Δ σ
    → ∃ λ level → Δ ⊢ substS σ T ⇒ tm-type level
  kind-transported {Γ = Γ} {Δ = Δ} {σ = σ} T l entry wf coh =
    l , T.subst⇒ {Γ = Γ} {Δ = Δ} {σ = σ} {t = T} {T = tm-type l} coh wf entry

  prefix-kind : ∀ {n d e} {Γ : Ctx n} {Δ : Ctx d} {Ε : Ctx e}
    {locals args tele name T l}
    → N.Declared Δ ((name , T) ∷ tele) Ε
    → Γ ⊢ T ⇒ tm-type l
    → WellFormed Δ
    → CheckedPrefix Γ locals args ((name , T) ∷ tele)
    → Frames.Coherent Γ Δ (F.prefix locals F.identity)
    → ∃ λ level → Δ ⊢ F.instantiatePrefix locals T ⇒ tm-type level
  prefix-kind {Γ = Γ} {Δ = Δ} {locals = locals} {T = T} {l = l}
    (N.dt∷ scoped entry-kind rest) kind wf prefix coh with kind-transported T l kind wf coh
  ... | level , typed =
    level , subst (λ A → Δ ⊢ A ⇒ tm-type level) (sym (prefix-equal′ locals T)) typed

  ----------------------------------------------------------------------
  -- DELIVERY 2: the positive argument comparator.
  --
  -- The comparator consumes the argument's REPLAYED inference derivation
  -- (never a checking derivation, and never a conversion witness) and
  -- decides whether it may be used at the declared expected type.
  --
  -- EXACT branch: the inferred type is syntactically the expected type, so
  -- `⇐-infer` + reflexivity accepts at ZERO fuel, with no model evaluation.
  --
  -- NON-EXACT branch: a bounded residual comparison of the argument's
  -- INFERRED TYPE against the declared expected type must succeed. The
  -- resulting conversion is used at the ORIGINAL expected type, never at
  -- the normal form, and the argument is never re-normalized into its own
  -- specification.
  ----------------------------------------------------------------------

  -- Comparison success under fresh slots is a native conversion of the
  -- two OPEN terms. This is the existing general theorem, not a new
  -- oracle; it is also why a coincident closing assignment cannot be
  -- used as an open-equality proof.
  compared-converts : ∀ {n} {left right : Term}
    → R.Supported n left → R.Supported n right
    → Compare.EqualResidual n (Fresh.environment n) left right
    → Conversion._≈_ C.W.M.conversion left right
  compared-converts {n} {left} {right} left-supported right-supported equal =
    subst (λ b → Conversion._≈_ C.W.M.conversion left b)
      (Fresh.identity {size = n} (R.scoped right-supported))
      (subst (λ a → Conversion._≈_ C.W.M.conversion a
               (substS (Meaning.environment-sub (Fresh.images n)) right))
        (Fresh.identity {size = n} (R.scoped left-supported))
        (EqualityProof.Sound.conversion source-checked (Fresh.scoped n)
          (Fresh.source-scope (R.scoped left-supported))
          (Fresh.source-scope (R.scoped right-supported)) (Fresh.denotes n) equal))

  -- Exact acceptance: the inferred type IS the expected type, so the
  -- conversion is reflexivity and no model evaluation is performed.
  exact-at : ∀ {n} {Γ : Ctx n} {argument expected inferred : Term}
    → inferred ≡ expected → (synthesized : Γ ⊢ argument ⇒ inferred)
    → ArgumentResult Γ argument expected
  exact-at {inferred = inferred} refl synthesized =
    exact (⇐-infer synthesized (Conversion.≈-refl C.W.M.conversion {t = inferred}))

  -- `synthesized` is the argument's REPLAYED inference derivation, at the
  -- type the replayer actually computed — which need NOT be the declared
  -- expected type. The comparison is between THAT INFERRED TYPE and the
  -- declared expected type, exactly as the closed checker does it; the
  -- argument itself is never re-normalized into its own specification.
  compared : ∀ {n} (fuel : ℕ) {Γ : Ctx n} {argument expected inferred : Term}
    → (synthesized : Γ ⊢ argument ⇒ inferred)
    → R.Supported n inferred → R.Supported n expected
    → ArgumentResult Γ argument expected
  compared {n} fuel {Γ = Γ} {argument = argument} {expected = expected} {inferred = inferred}
    synthesized inf-supported exp-supported
    with Syntax.equal? inferred expected
  ... | yes same = exact-at same synthesized
  ... | no different
    with Compare.compare-with C.W.ind fuel n (Fresh.environment n) inferred expected
  ...   | Compare.same equal = normalized
    (⇐-infer {t = argument} {T = expected} {T′ = inferred} synthesized
      (compared-converts {n = n} {left = inferred} {right = expected}
        inf-supported exp-supported equal))
    equal
  ... | Compare.distinct forms = distinct-forms
    (Compare.DistinctResidual.left-form forms) (Compare.DistinctResidual.right-form forms)
  ... | Compare.unknown side reason = inconclusive side reason

  compare-argument : ∀ {n} (fuel : ℕ) (Γ : Ctx n)
    → {argument expected inferred : Term}
    → (synthesized : Γ ⊢ argument ⇒ inferred)
    → R.Supported n inferred → R.Supported n expected
    → Options → ArgumentResult Γ argument expected
  compare-argument {n} fuel Γ {argument} {expected} {inferred} synthesized
    inf-supported exp-supported opts
    with Options.residual opts | Syntax.equal? inferred expected
  ... | false | yes same = exact-at same synthesized
  ... | false | no different = inconclusive Compare.left-side E.unsupported
  ... | true | yes same = exact-at same synthesized
  ... | true | no different = compared {n = n} fuel synthesized inf-supported exp-supported

  -- The positive outcomes, as the checking derivation they carry. This is
  -- what the caller path consumes; the negative outcomes carry no proof.
  checked-argument : ∀ {n} {Γ : Ctx n} {argument expected : Term}
    → ArgumentResult Γ argument expected → Maybe (Γ ⊢ argument ⇐ expected)
  checked-argument (exact checked) = just checked
  checked-argument (normalized checked equal) = just checked
  checked-argument (distinct-forms left right) = nothing
  checked-argument (inconclusive side reason) = nothing

  ----------------------------------------------------------------------
  -- DELIVERY 3: caller integration. The comparator's evidence is turned
  -- back into the EXISTING exact spine judgment and the existing coherent
  -- complete frame, so every downstream theorem (closing substitution,
  -- original-goal admission, trace/fuel/tree safety) is reused unchanged.
  ----------------------------------------------------------------------

  prefix-spine : ∀ {n} {Γ : Ctx n} {locals args tele}
    → CheckedPrefix Γ locals args tele → Spine Γ locals args tele
  prefix-spine cp[] = sp[]
  prefix-spine (cp∷ final checked rest) = sp∷ checked (prefix-spine rest)

  instantiate : ∀ {n d e} {Γ : Ctx n} {Δ : Ctx d} {Ε : Ctx e} {locals args tele}
    → N.Declared Δ tele Ε
    → CheckedPrefix Γ locals args tele
    → Frames.Coherent Δ Γ (F.prefix locals F.identity)
    → Spine Γ locals args tele
      × Frames.Coherent Ε Γ (F.advance args (F.prefix locals F.identity))
  instantiate declaration prefix coh =
    prefix-spine prefix , prefix-coherent declaration prefix coh
