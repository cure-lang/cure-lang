------------------------------------------------------------------------
-- Pure suffix regressions with a dependent field and ambient binder.
-- Evidence is uniformly native in one ind/sig/conv; no validity oracle.
------------------------------------------------------------------------
module Proof.DependentContextSuffixExamples where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature using (IndEnv; Telescope)
open import Core.Reduction using (Signature)
open import Core.Universe using (l0; l1)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.DependentTyping using (Opened; op[]; op∷)
import Core.DependentTyping as Native
open import Proof.DependentContextSuffix

module Examples (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  open ContextSuffix ind sig conv

  Γ : Ctx 1
  Γ = extend ⟨⟩ tm-int_type

  wfΓ : WellFormed Γ
  wfΓ = wf∷ wf[] sc-int_type ⇒-int_type

  tele : Telescope
  tele = ("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ []

  Θ : Ctx 3
  Θ = extend (extend Γ (tm-type l0)) (tm-var 0)

  opened : Opened Γ tm-var tele Θ
  opened = op∷ (op∷ op[])

  wfΘ : WellFormed Θ
  wfΘ = wf∷ (wf∷ wfΓ sc-type (⇒-type refl))
    (sc-var (s≤s z≤n)) (⇒-var zero)

  recover-exact-context :
    context (drop 2 (wctx wfΘ)) ≡ (1 , Γ)
  recover-exact-context = drop-opened opened wfΘ

  recover-original-proof : drop 2 (wctx wfΘ) ≡ wctx wfΓ
  recover-original-proof = refl

  recover-prefix : WellFormed Γ
  recover-prefix = prefix-WF opened wfΘ

  snoc-diagram : OpenedSnoc Γ tm-var tele Θ
  snoc-diagram = opened-snoc opened

  forward-again : Opened Γ tm-var tele Θ
  forward-again = snoc-opened snoc-diagram

  -- The exposed kind proof is the original variable derivation, not the
  -- result of invoking a transport theorem on the declaration.
  original-kind : LastWF.kind (last-WF wfΘ) ≡ ⇒-var zero
  original-kind = refl

  exact-drop-composition :
    drop (1 + 1) (wctx wfΘ) ≡ drop 1 (drop 1 (wctx wfΘ))
  exact-drop-composition = drop-compose 1 1 (wctx wfΘ)

  -- Overdropping is explicitly saturating at the real empty WF prefix.
  saturating : drop 4 (wctx wfΘ) ≡ wctx wf[]
  saturating = refl

-- Both square regressions protect the fresh field 0 while transforming
-- the ambient reference underneath it.
rename-dependent-square : ∀ ρ
  → rename (ext ρ) (substS (extSub (λ i → tm-var i)) (tm-var 1))
    ≡ substS (extSub (λ i → rename ρ (tm-var i))) (tm-var 1)
rename-dependent-square ρ = rename-opening-square 1 ρ tm-var (tm-var 1)

subst-dependent-square : ∀ τ
  → substS (extSub τ) (substS (extSub tm-var) (tm-var 1))
    ≡ substS (extSub (λ i → substS τ (tm-var i))) (tm-var 1)
subst-dependent-square τ = subst-opening-square 1 τ tm-var (tm-var 1)
