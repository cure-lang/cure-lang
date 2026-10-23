{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- General positive native data readback under a checked finite layout.
-- Canonical split/field denotation is explicit, not an evaluation oracle.
------------------------------------------------------------------------
module Proof.DataReadback where

open import Data.List using ([]; _∷_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import Core.Syntax
open import Core.Reduction using (Signature; _⇝_; _⇝*_; ⇝*-refl; ⇝*-step;
  ξ-data-params-at; ξ-data-indices-at)
import Core.DataSpine as Layout
import Core.DataReadback as Read
import Core.ClosureScope as Scope
import Core.ClosureQuote as Q
import Core.ClosureEval as E
import Proof.ClosureEvaluation as Meaning
import Proof.ClosureQuotation as Quote
import Core.CheckedAdmission as Admission
import Core.CallerAdmission as Caller
import Proof.Substitution as Substitution

cut-scope : ∀ {d n values ps is} → Layout.Cut n values ps is → Scope.EnvironmentScoped d values
  → Scope.EnvironmentScoped d ps × Scope.EnvironmentScoped d is
cut-scope Layout.cut-zero scope = Scope.s[] , scope
cut-scope (Layout.cut-cons rest) (Scope.s∷ head tail) with cut-scope rest tail
... | params , indices = Scope.s∷ head params , indices

no-delta-step : ∀ {d ind name values endpoint} (out : Read.Output d ind name values)
  → _⇝_ Quote.no-delta (Read.Output.term out) endpoint → ⊥
no-delta-step out (ξ-data-params-at i step) = Quote.spine-no-step
  (Q.spine-normal (Read.Output.parameters-quoted out)) i step
no-delta-step out (ξ-data-indices-at i step) = Quote.spine-no-step
  (Q.spine-normal (Read.Output.indices-quoted out)) i step

module Simulation (sig : Signature) where
  module Quotation = Quote.Simulation sig
  module O = Quotation.O
  to-parallel : ∀ {t u} → _⇝*_ sig t u → O._⇉*_ t u
  to-parallel = Quotation.Eval.to-parallel
  spine : ∀ {d values terms quoted} → Scope.EnvironmentScoped d values → Meaning.Environments d values terms
    → Q.SpineQuoted d values quoted → O._⇉*ᵗ*_ terms quoted
  spine = Quotation.spine-parallel

  quotation : ∀ {d ind name values ps is} (out : Read.Output d ind name values)
    → Scope.EnvironmentScoped d values
    → Meaning.Environments d (Layout.Alignment.parameters (Read.Output.alignment out)) ps
    → Meaning.Environments d (Layout.Alignment.indices (Read.Output.alignment out)) is
    → _⇝*_ sig (tm-data name ps is) (Read.Output.term out)
  quotation {ps = ps} {is} out scope params indices
    with cut-scope (Layout.Alignment.parameter-prefix (Read.Output.alignment out)) scope
  ... | ps-scope , is-scope = O.⇉→⇝*-star (O.⇉*-trans
    (O.⇉*-data-params* [] ps _ is (spine ps-scope params (Read.Output.parameters-quoted out)))
    (O.⇉*-data-indices* [] is _ _ (spine is-scope indices (Read.Output.indices-quoted out))))

  evaluated-spine : ∀ {d env terms args values} → Meaning.Environments d env terms
    → E.EvaluatesSpine env args values
    → ∃ λ results → Meaning.Environments d values results ×
      O._⇉*ᵗ*_ (substTermsS (Meaning.environment-sub terms) args) results
  evaluated-spine = Quotation.Eval.parallel-spine

  normalization : ∀ {d ind name values env terms ps is} (out : Read.Output d ind name values)
    → Scope.EnvironmentScoped d values → Meaning.Environments d env terms
    → E.EvaluatesSpine env ps (Layout.Alignment.parameters (Read.Output.alignment out))
    → E.EvaluatesSpine env is (Layout.Alignment.indices (Read.Output.alignment out))
    → _⇝*_ sig (tm-data name (substTermsS (Meaning.environment-sub terms) ps)
        (substTermsS (Meaning.environment-sub terms) is)) (Read.Output.term out)
  normalization out scope env params indices
    with evaluated-spine env params | evaluated-spine env indices
  ... | ps , ps-denoted , ps-path | is , is-denoted , is-path = O.⇝*-trans
    (O.⇉→⇝*-star (O.⇉*-trans (O.⇉*-data-params* [] _ ps _ ps-path)
      (O.⇉*-data-indices* [] _ is ps is-path)))
    (quotation out scope ps-denoted is-denoted)

module Safe {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module R = Caller.Replay source-checked
  module C = R.C
  module Model = Simulation C.W.sig
  safe-readback : ∀ {request name values ps is} (admitted : R.Checked request)
    → (out : Read.Output 0 C.W.ind name values)
    → R.Checked.closed-subject admitted ≡ tm-data name ps is
    → Scope.EnvironmentScoped 0 values
    → E.EvaluatesSpine [] ps (Layout.Alignment.parameters (Read.Output.alignment out))
    → E.EvaluatesSpine [] is (Layout.Alignment.indices (Read.Output.alignment out))
    → C.Sound.SafeState (Read.Output.term out) (R.Checked.closed-goal admitted)
  safe-readback {name = name} {ps = ps} {is} admitted out shape scope params indices =
    R.Checked.trace-safe admitted
      (Model.O.⇝*-source (trans (Substitution.substS-idSub (tm-data name ps is)) (sym shape))
        (Model.normalization out scope Meaning.d[] params indices))
