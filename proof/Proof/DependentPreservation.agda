------------------------------------------------------------------------
-- Operational preservation for the BOUNDED base-checked registry layer.
-- This is constructor congruence, not dependent case elimination or
-- preservation of the full unified Core typing relation.
------------------------------------------------------------------------
module Proof.DependentPreservation where

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature using (IndEnv; fam-name; ctor-indices)
open import Core.Reduction
open import Core.Typing using (Ctx; Conversion; All2; a2[]; a2∷)
import Core.LocalFrame as F
open import Proof.Progress using (FinalTerms; ft[]; ft∷; BuiltinCtors; Certified)
open import Proof.Preservation using (ClosedFragmentSig; ReduceConv; CertifiedTyped)
open import Proof.FinalPreservation using (final-preservation)
import Proof.DependentRegistry as Registry

module Preserve (base : IndEnv) (sig : Signature) (conv : Conversion) (registry : IndEnv)
  (closed : ClosedFragmentSig base sig) (rc : ReduceConv sig conv)
  (typed : CertifiedTyped base sig conv) (bc : BuiltinCtors base) (cert : Certified sig) where
  module L = Registry.Layer base sig conv registry
  module A = L.Admission closed rc typed bc cert
  module P = A.P
  open Core.Typing.Typing base sig conv
  open L.T using (Arguments; as[]; as∷)

  _≈_ = Conversion._≈_ conv

  refl-terms : ∀ xs → All2 _≈_ xs xs
  refl-terms [] = a2[]
  refl-terms (x ∷ xs) = a2∷ (Conversion.≈-refl conv {t = x}) (refl-terms xs)

  prefix-converts : ∀ {xs ys} → All2 _≈_ xs ys → ∀ k i
    → argsSub-go k xs i ≈ argsSub-go k ys i
  prefix-converts a2[] k i = Conversion.≈-refl conv
  prefix-converts (a2∷ equal rest) k zero = equal
  prefix-converts (a2∷ equal rest) k (suc i) = prefix-converts rest (suc k) i

  -- A changed earlier value changes later expected TYPES. Convert the
  -- checking goals; do not pretend the raw instantiated types are equal.
  convert-arguments : ∀ {n} {Γ : Ctx n} {old new args tele}
    → All2 _≈_ old new → Arguments Γ old args tele → Arguments Γ new args tele
  convert-arguments equal as[] = as[]
  convert-arguments {old = old} {new = new} equal
    (as∷ {arg = arg} {T = T} checked rest) =
    as∷ (⇐-conv checked (Conversion.≈-subst-cong conv
      {t = T} {σ = argsSub old} {σ′ = argsSub new} (prefix-converts equal 0)))
      (convert-arguments (a2∷ (Conversion.≈-refl conv {t = arg}) equal) rest)

  arguments-preserve-at : ∀ {n} {Γ : Ctx n} {locals args tele}
    (i : Fin (len args)) {arg′}
    → FinalTerms args → Arguments Γ locals args tele
    → _⇝_ sig (lookupAt args i) arg′
    → Arguments Γ locals (setAt args i arg′) tele
  arguments-preserve-at {locals = locals} zero (ft∷ final finals) (as∷ checked rest) step =
    as∷ (P.preservation final checked step)
      (convert-arguments (a2∷ (rc step) (refl-terms locals)) rest)
  arguments-preserve-at (suc i) (ft∷ final finals) (as∷ checked rest) step =
    as∷ checked (arguments-preserve-at i finals rest step)

  final-preserve-at : ∀ {args} (i : Fin (len args)) {arg′}
    → FinalTerms args → _⇝_ sig (lookupAt args i) arg′ → FinalTerms (setAt args i arg′)
  final-preserve-at zero (ft∷ final finals) step =
    ft∷ (final-preservation sig cert final step) finals
  final-preserve-at (suc i) (ft∷ final finals) step = ft∷ final (final-preserve-at i finals step)

  update-converts : ∀ args (i : Fin (len args)) {arg′}
    → _⇝_ sig (lookupAt args i) arg′ → All2 _≈_ args (setAt args i arg′)
  update-converts (x ∷ xs) zero step = a2∷ (rc step) (refl-terms xs)
  update-converts (x ∷ xs) (suc i) step =
    a2∷ (Conversion.≈-refl conv {t = x}) (update-converts xs i step)

  push-converts : ∀ {x y σ τ} → x ≈ y → (∀ i → σ i ≈ τ i)
    → ∀ i → F.push x σ i ≈ F.push y τ i
  push-converts equal locals zero = equal
  push-converts equal locals (suc i) = locals i

  advance-converts : ∀ {xs ys σ τ} → All2 _≈_ xs ys → (∀ i → σ i ≈ τ i)
    → ∀ i → F.advance xs σ i ≈ F.advance ys τ i
  advance-converts a2[] locals i = locals i
  advance-converts (a2∷ equal rest) locals = advance-converts rest (push-converts equal locals)

  instantiate-converts : ∀ ts {σ τ} → (∀ i → σ i ≈ τ i)
    → All2 _≈_ (map (substS σ) ts) (map (substS τ) ts)
  instantiate-converts [] equal = a2[]
  instantiate-converts (t ∷ ts) {σ} {τ} equal =
    a2∷ (Conversion.≈-subst-cong conv {t = t} {σ = σ} {σ′ = τ} equal)
      (instantiate-converts ts equal)

  update-application : ∀ {n} {Γ : Ctx n} {name ps args}
    → L.Application Γ name ps args → (i : Fin (len args)) → ∀ {arg′}
    → _⇝_ sig (lookupAt args i) arg′ → L.Application Γ name ps (setAt args i arg′)
  update-application app i step = record
    { registry-valid = L.Application.registry-valid app
    ; family = L.Application.family app ; ctor = L.Application.ctor app
    ; found = L.Application.found app ; parameters = L.Application.parameters app
    ; fields = arguments-preserve-at i (L.Application.fields-final app) (L.Application.fields app) step
    ; parameters-final = L.Application.parameters-final app
    ; fields-final = final-preserve-at i (L.Application.fields-final app) step }

  result-type : ∀ {n} {Γ : Ctx n} {name ps args} → L.Application Γ name ps args → Term
  result-type {ps = ps} {args = args} app =
    tm-data (fam-name (L.Application.family app)) ps
      (F.instantiateResults ps args (ctor-indices (L.Application.ctor app)))

  result-update-converts : ∀ {n} {Γ : Ctx n} {name ps args}
    → (app : L.Application Γ name ps args) → (i : Fin (len args)) → ∀ {arg′}
    → (step : _⇝_ sig (lookupAt args i) arg′)
    → result-type app ≈ result-type (update-application app i step)
  result-update-converts {ps = ps} {args = args} app i step =
    Conversion.≈-data conv (refl-terms ps)
      (instantiate-converts (ctor-indices (L.Application.ctor app))
        (advance-converts (update-converts args i step) (λ j → Conversion.≈-refl conv)))

  -- Fixed-goal checking is essential: merely reporting the newly computed
  -- result type would not be a preservation theorem.
  record CheckedApplication {n} (Γ : Ctx n) (name : Name) (ps args : List Term) (goal : Term) : Set where
    field
      application : L.Application Γ name ps args
      at-goal : result-type application ≈ goal
  open CheckedApplication public

  preserve-at : ∀ {n} {Γ : Ctx n} {name ps args goal}
    → CheckedApplication Γ name ps args goal → (i : Fin (len args)) → ∀ {arg′}
    → _⇝_ sig (lookupAt args i) arg′
    → CheckedApplication Γ name ps (setAt args i arg′) goal
  preserve-at {goal = goal} checked i step = record
    { application = updated
    ; at-goal = Conversion.≈-trans conv {t = result-type updated} {u = result-type original} {v = goal}
        (Conversion.≈-sym conv {t = result-type original} {u = result-type updated}
          (result-update-converts original i step)) (at-goal checked) }
    where
      original = application checked
      updated = update-application original i step

  preserve-step : ∀ {n} {Γ : Ctx n} {name ps args goal t′}
    → CheckedApplication Γ name ps args goal → _⇝_ sig (tm-ctor name args) t′
    → Σ (List Term) (λ args′ → t′ ≡ tm-ctor name args′ × CheckedApplication Γ name ps args′ goal)
  preserve-step {args = args} checked (ξ-ctor-at i {x′ = x′} step) =
    setAt args i x′ , refl , preserve-at checked i step

  preserve-star : ∀ {n} {Γ : Ctx n} {name ps args goal t′}
    → CheckedApplication Γ name ps args goal → _⇝*_ sig (tm-ctor name args) t′
    → Σ (List Term) (λ args′ → t′ ≡ tm-ctor name args′ × CheckedApplication Γ name ps args′ goal)
  preserve-star {args = args} checked ⇝*-refl = args , refl , checked
  preserve-star checked (⇝*-step (ξ-ctor-at i step) rest) =
    preserve-star (preserve-at checked i step) rest
