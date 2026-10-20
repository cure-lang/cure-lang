------------------------------------------------------------------------
-- Native progress needs no signature-validity, positivity or layout
-- premise. Coverage and constructor arities come from native derivations.
------------------------------------------------------------------------
module Proof.DependentProgress where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Coverage
open import Core.Typing using (⟨⟩; Conversion)
open import Core.DependentTyping
open import Proof.Progress public using (Final; FinalTerms; FinalBranches)
open Final
import Proof.DependentCanonical as CF
import Proof.DependentConstructorInversion as CI

module Progress (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.DependentTyping.Typing ind sig conv
  open CF.Laws ind sig conv
  open CI.Laws ind sig conv using (constructor-inference; module ConstructorView)
  open ConstructorView

  ProgressResult : Term → Set
  ProgressResult t = Value t ⊎ (∃ λ u → _⇝_ sig t u)

  case-ctor-step : ∀ {c args name ps is motive brs}
    → ⟨⟩ ⊢ tm-ctor c args ⇒ tm-data name ps is
    → CaseCoverage ind name brs
    → ProgressResult (tm-case (tm-ctor c args) motive brs)
  case-ctor-step {args = args} der covered with constructor-inference der
  ... | view with ctor-covered covered (found view) (data-name (result-conversion view))
  ... | b , branch = inj₂ (substArgs args b , ι branch (spine-length (fields-checked view)))

  case-nat-step : ∀ {name} (k : ℕ) (brs : List Branch) (m : Term)
    → IndEnv.builtins ind "nat" ≡ just name
    → CaseCoverage ind name brs
    → ProgressResult (tm-case (tm-nat_lit k) m brs)
  case-nat-step zero brs m builtin covered with nat-zero-covered covered builtin
  ... | b , branch = inj₂ (substArgs [] b , ι-nat-zero branch refl)
  case-nat-step (suc k) brs m builtin covered with nat-suc-covered covered builtin
  ... | b , branch = inj₂ (substArgs (tm-nat_lit k ∷ []) b , ι-nat-suc branch refl)

  case-bounded-step : ∀ {name} (k : ℕ) (brs : List Branch) (m : Term)
    → IndEnv.builtins ind "bounded" ≡ just name
    → CaseCoverage ind name brs
    → ProgressResult (tm-case (tm-bounded_lit k) m brs)
  case-bounded-step zero brs m builtin covered with bounded-zero-covered covered builtin
  ... | b , branch = inj₂ (substArgs (tm-nat_lit zero ∷ []) b , ι-bounded-zero branch refl)
  case-bounded-step (suc k) brs m builtin covered with bounded-suc-covered covered builtin
  ... | b , branch = inj₂
    (substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b , ι-bounded-suc branch refl)

  mutual
    progress⇒ : ∀ {t T} → ⟨⟩ ⊢ t ⇒ T → Final t → ProgressResult t
    progress⇒ (⇒-var ()) ff
    progress⇒ (⇒-type p) ff = inj₁ (canonical c-type)
    progress⇒ (⇒-pi p q) (f-pi fd fc) = inj₁ (canonical c-pi)
    progress⇒ (⇒-lam p q) (f-lam fd fb) = inj₁ (canonical c-lam)
    progress⇒ ⇒-int_type ff = inj₁ (canonical c-int_type)
    progress⇒ ⇒-float_type ff = inj₁ (canonical c-float_type)
    progress⇒ ⇒-binary_type ff = inj₁ (canonical c-binary_type)
    progress⇒ ⇒-atom_type ff = inj₁ (canonical c-atom_type)
    progress⇒ ⇒-int_lit ff = inj₁ (canonical c-int_lit)
    progress⇒ ⇒-float_lit ff = inj₁ (canonical c-float_lit)
    progress⇒ ⇒-atom_lit ff = inj₁ (canonical c-atom_lit)
    progress⇒ (⇒-nat_lit p q r s) ff = inj₁ (canonical c-nat_lit)
    progress⇒ (⇒-bounded_lit p q r s) ff = inj₁ (canonical c-bounded_lit)
    progress⇒ (⇒-data p q r) (f-data fps fis) = inj₁ (canonical c-data)
    progress⇒ (⇒-ctor p q r) (f-ctor fargs) = inj₁ (canonical c-ctor)
    progress⇒ (⇒-effect_type p) (f-effect_type ft) = inj₁ (canonical c-effect_type)
    progress⇒ (⇒-effect_pure p) (f-effect_pure ft) = inj₁ (canonical c-effect_pure)
    progress⇒ (⇒-effect_bind p q) (f-effect_bind fe fk) = inj₁ (canonical c-effect_bind)
    progress⇒ (⇒-app {f = f} {a = a} p q) (f-app ff fa) with progress⇒ p ff
    ... | inj₂ (f′ , step) = inj₂ (tm-app f′ a , ξ-app₁ step)
    ... | inj₁ (neutral nf) = inj₁ (neutral (n-app nf))
    ... | inj₁ (canonical cf) with canonical-pi p cf
    ... | g , d , b , refl with progress⇒ q fa
    ... | inj₂ (a′ , step) = inj₂ (tm-app (tm-lam g d b) a′ , ξ-app₂ step)
    ... | inj₁ av = inj₂ (substTopT a b , β)
    progress⇒ (⇒-let {v = v} {b = b} p q r) (f-let fty fv fb) with progress⇐ q fv
    ... | inj₂ (v′ , step) = inj₂ (tm-let _ _ v′ b , ξ-let step)
    ... | inj₁ vv = inj₂ (substTopT v b , ζ)
    progress⇒ (⇒-global {name = name} p) ff with Signature.body sig name in eq
    ... | just b = inj₂ (b , δ eq)
    ... | nothing = inj₁ (neutral n-global)
    progress⇒ (⇒-case {s = s} {motive = m} {brs = brs}
      wf found p pars indices mot branches covered) (f-case fs fm fbs)
      with progress⇒ p fs
    ... | inj₂ (s′ , step) = inj₂ (tm-case s′ m brs , ξ-case step)
    ... | inj₁ (neutral ns) = inj₁ (neutral (n-case ns))
    ... | inj₁ (canonical cs) with canonical-data p cs
    ... | inj₁ (c , args , refl) = case-ctor-step p covered
    ... | inj₂ (inj₁ (k , refl)) = case-nat-step k brs m (nat-lit-family p) covered
    ... | inj₂ (inj₂ (k , refl)) =
      case-bounded-step k brs m (bounded-lit-family p) covered
    progress⇒ (⇒-conv der eq) ff = progress⇒ der ff
    progress⇒ (⇒-cumul der le) ff = progress⇒ der ff

    progress⇐ : ∀ {t T} → ⟨⟩ ⊢ t ⇐ T → Final t → ProgressResult t
    progress⇐ (⇐-lam p q) (f-lam fd fb) = inj₁ (canonical c-lam)
    progress⇐ ⇐-hole ()
    progress⇐ (⇐-infer der eq) ff = progress⇒ der ff
    progress⇐ (⇐-conv der eq) ff = progress⇐ der ff
    progress⇐ (⇐-cumul der le) ff = progress⇒ der ff

  progress : ∀ {t T} → ⟨⟩ ⊢ t ⇒ T → Final t → ProgressResult t
  progress = progress⇒
