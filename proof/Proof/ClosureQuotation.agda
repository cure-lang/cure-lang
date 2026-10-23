------------------------------------------------------------------------
-- General positive Quote MODEL refinement. Captured-body scope and
-- scoped environment weakening are PROVED inputs, not normalization
-- callbacks. Globals stay neutral; no eta or delta claim is made.
------------------------------------------------------------------------
module Proof.ClosureQuotation where

open import Data.Nat using (suc)
open import Data.List using (length; []; _∷_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
open import Core.Syntax
open import Core.Reduction using (Signature; _⇝_; _⇝*_; ⇝*-refl;
  β; δ; ξ-pi-dom; ξ-pi-cod; ξ-lam-dom; ξ-lam-body; ξ-app₁; ξ-app₂; ξ-ctor-at;
  ξ-data-params-at; ξ-data-indices-at)
import Core.ClosureScope as S
import Core.ClosureQuote as Q
import Core.FlatContext as Flat
import Proof.ClosureEvaluation as M
import Proof.ClosureWeakening as W

-- No positive Quote result is asserted to be irreducible under an
-- arbitrary certified-delta signature.
no-delta : Signature
no-delta = record { body = λ _ → nothing ; type-of = λ _ → nothing }
mutual
  normal-no-step : ∀ {term endpoint} → Q.BetaZetaNormal term → _⇝_ no-delta term endpoint → ⊥
  normal-no-step Q.normal-type ()
  normal-no-step Q.normal-atom-type ()
  normal-no-step Q.normal-atom ()
  normal-no-step (Q.normal-ctor fields) (ξ-ctor-at i step) = spine-no-step fields i step
  normal-no-step (Q.normal-data params indices) (ξ-data-params-at i step) = spine-no-step params i step
  normal-no-step (Q.normal-data params indices) (ξ-data-indices-at i step) = spine-no-step indices i step
  normal-no-step (Q.normal-pi domain body) (ξ-pi-dom step) = normal-no-step domain step
  normal-no-step (Q.normal-pi domain body) (ξ-pi-cod step) = normal-no-step body step
  normal-no-step (Q.normal-lam domain body) (ξ-lam-dom step) = normal-no-step domain step
  normal-no-step (Q.normal-lam domain body) (ξ-lam-body step) = normal-no-step body step
  normal-no-step (Q.normal-neutral head) step = neutral-no-step head step
  neutral-no-step : ∀ {term endpoint} → Q.NeutralNormal term → _⇝_ no-delta term endpoint → ⊥
  neutral-no-step Q.normal-var ()
  neutral-no-step Q.normal-global (δ ())
  neutral-no-step (Q.normal-app () argument) β
  neutral-no-step (Q.normal-app function argument) (ξ-app₁ step) = neutral-no-step function step
  neutral-no-step (Q.normal-app function argument) (ξ-app₂ step) = normal-no-step argument step
  spine-no-step : ∀ {terms endpoint} → Q.SpineNormal terms → (i : Fin (len terms))
    → _⇝_ no-delta (lookupAt terms i) endpoint → ⊥
  spine-no-step (Q.normal∷ head rest) zero step = normal-no-step head step
  spine-no-step (Q.normal∷ head rest) (suc i) step = spine-no-step rest i step

module Simulation (sig : Signature) where
  module Eval = M.Simulation sig
  module O = Eval.O
  mutual
    quotation : ∀ {depth value term quoted} → S.ValueScoped depth value
      → M.Denotes depth value term → Q.Quoted depth value quoted → _⇝*_ sig term quoted
    quotation S.s-type M.d-type Q.q-type = ⇝*-refl
    quotation S.s-atom-type M.d-atom-type Q.q-atom-type = ⇝*-refl
    quotation S.s-atom M.d-atom Q.q-atom = ⇝*-refl
    quotation (S.s-ctor fields) (M.d-ctor denoted) (Q.q-ctor quoted) = spine-quotation fields denoted quoted _
    quotation (S.s-data ps is) (M.d-data params indices) (Q.q-data quoted-ps quoted-is) =
      O.⇉→⇝*-star (O.⇉*-trans
        (O.⇉*-data-params* [] _ _ _ (spine-parallel ps params quoted-ps))
        (O.⇉*-data-indices* [] _ _ _ (spine-parallel is indices quoted-is)))
    quotation {depth} (S.s-pi domain-scope env-scope body-scope)
      (M.d-pi {body = body} {terms = terms} domain env)
      (Q.q-pi evaluated domain-quoted body-quoted)
      with Eval.evaluate (M.d∷ (M.flat-denotation (Flat.fresh depth)) (W.environments env-scope env)) evaluated
    ... | result , denoted , path = O.⇝*-trans
      (O.⇝*-pi-dom (quotation domain-scope domain domain-quoted))
      (O.⇝*-pi-cod (O.⇝*-trans
        (Eval.equal-path (W.open-body terms body (W.capture-scope env body-scope)))
        (O.⇝*-trans path (quotation
          (S.evaluate-scoped
            (S.s∷ (S.s-neutral (S.s-var (Nat.n<1+n depth))) (S.raise-environment env-scope))
            body-scope evaluated) denoted body-quoted))))
    quotation {depth} (S.s-lam domain-scope env-scope body-scope)
      (M.d-lam {body = body} {terms = terms} domain env)
      (Q.q-lam evaluated domain-quoted body-quoted)
      with Eval.evaluate (M.d∷ (M.flat-denotation (Flat.fresh depth)) (W.environments env-scope env)) evaluated
    ... | result , denoted , path = O.⇝*-trans
      (O.⇝*-lam-dom (quotation domain-scope domain domain-quoted))
      (O.⇝*-lam-body (O.⇝*-trans
        (Eval.equal-path (W.open-body terms body (W.capture-scope env body-scope)))
        (O.⇝*-trans path (quotation
          (S.evaluate-scoped
            (S.s∷ (S.s-neutral (S.s-var (Nat.n<1+n depth))) (S.raise-environment env-scope))
            body-scope evaluated) denoted body-quoted))))
    quotation (S.s-neutral head-scope) (M.d-neutral head) (Q.q-neutral quoted) =
      neutral-quotation head-scope head quoted

    neutral-quotation : ∀ {depth value term quoted} → S.NeutralScoped depth value
      → M.Neutrals depth value term → Q.NeutralQuoted depth value quoted → _⇝*_ sig term quoted
    neutral-quotation (S.s-var inside) (M.d-var bounded) (Q.q-var quoted-bound) = ⇝*-refl
    neutral-quotation S.s-global M.d-global Q.q-global = ⇝*-refl
    neutral-quotation (S.s-app function-scope argument-scope) (M.d-app function argument)
      (Q.q-app function-quoted argument-quoted) = O.⇝*-trans
        (O.⇝*-app₁ (neutral-quotation function-scope function function-quoted))
        (O.⇝*-app₂ (quotation argument-scope argument argument-quoted))

    spine-quotation : ∀ {depth values terms quoted} → S.EnvironmentScoped depth values
      → M.Environments depth values terms → Q.SpineQuoted depth values quoted
      → ∀ name → _⇝*_ sig (tm-ctor name terms) (tm-ctor name quoted)
    spine-quotation S.s[] M.d[] Q.q[] name = ⇝*-refl
    spine-quotation (S.s∷ head rest) (M.d∷ denoted environment) (Q.q∷ quoted quotes) name =
      O.⇝*-trans (O.⇝*-at-ctor _ zero (quotation head denoted quoted))
        (O.⇝*-ctor-tail-shift _ (spine-quotation rest environment quotes name))

    spine-parallel : ∀ {depth values terms quoted} → S.EnvironmentScoped depth values
      → M.Environments depth values terms → Q.SpineQuoted depth values quoted → O._⇉*ᵗ*_ terms quoted
    spine-parallel S.s[] M.d[] Q.q[] = O.⇉ᵗ*-nil
    spine-parallel (S.s∷ head rest) (M.d∷ denoted environment) (Q.q∷ quoted quotes) =
      O.⇉ᵗ*-cons (Eval.to-parallel (quotation head denoted quoted)) (spine-parallel rest environment quotes)

  normalization : ∀ {depth env terms term quoted}
    → S.EnvironmentScoped depth env → Scoped (length env) term → M.Environments depth env terms
    → Q.Normalizes depth env term quoted
    → _⇝*_ sig (substS (M.environment-sub terms) term) quoted
  normalization env-scope term-scope env execution
    with Eval.evaluate env (Q.Normalizes.evaluated execution)
  ... | result , denoted , path = O.⇝*-trans path
    (quotation (S.evaluate-scoped env-scope term-scope (Q.Normalizes.evaluated execution))
      denoted (Q.Normalizes.quoted execution))
