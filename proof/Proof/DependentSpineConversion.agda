------------------------------------------------------------------------
-- Native conversion algebra. No preservation or transport premise.
-- Canonical frames agree at EVERY index, including beyond the prefix.
------------------------------------------------------------------------
module Proof.DependentSpineConversion where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature; argsSub; argsSub-go)
open import Core.Typing using (Ctx; Conversion; All2; a2[]; a2∷; surface-field-vars)
import Core.DependentTyping as Native
import Core.LocalFrame as F

module Laws (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  open Conversion conv

  abstract
    all2-length : ∀ {xs ys} → All2 _≈_ xs ys → length xs ≡ length ys
    all2-length a2[] = refl
    all2-length (a2∷ equal rest) = cong suc (all2-length rest)

    all2-refl : ∀ xs → All2 _≈_ xs xs
    all2-refl [] = a2[]
    all2-refl (x ∷ xs) = a2∷ (≈-refl {t = x}) (all2-refl xs)

    argsSub-go-cong : ∀ n {xs ys} → All2 _≈_ xs ys
      → ∀ k → argsSub-go n xs k ≈ argsSub-go n ys k
    argsSub-go-cong n a2[] k = ≈-refl {t = tm-var k}
    argsSub-go-cong n (a2∷ equal rest) zero = equal
    argsSub-go-cong n (a2∷ equal rest) (suc k) =
      argsSub-go-cong (suc n) rest k

    argsSub-cong : ∀ {xs ys} → All2 _≈_ xs ys
      → ∀ k → argsSub xs k ≈ argsSub ys k
    argsSub-cong equal = argsSub-go-cong zero equal

    prefix-cong : ∀ {locals locals′} → All2 _≈_ locals locals′
      → ∀ T → F.instantiatePrefix locals T ≈ F.instantiatePrefix locals′ T
    prefix-cong {locals} {locals′} equal T =
      ≈-subst-cong {t = T} {σ = argsSub locals} {σ′ = argsSub locals′}
        (argsSub-cong equal)

    push-cong : ∀ {x y σ τ} → x ≈ y
      → (∀ k → σ k ≈ τ k) → ∀ k → F.push x σ k ≈ F.push y τ k
    push-cong equal base zero = equal
    push-cong equal base (suc k) = base k

    advance-cong : ∀ {xs ys σ τ} → All2 _≈_ xs ys
      → (∀ k → σ k ≈ τ k)
      → ∀ k → F.advance xs σ k ≈ F.advance ys τ k
    advance-cong a2[] base k = base k
    advance-cong (a2∷ equal rest) base k =
      advance-cong rest (push-cong equal base) k

    result-frame-cong : ∀ {ps ps′ fields fields′}
      → All2 _≈_ ps ps′ → All2 _≈_ fields fields′
      → ∀ k → F.advance fields (F.advance ps F.identity) k
        ≈ F.advance fields′ (F.advance ps′ F.identity) k
    result-frame-cong pars fields k =
      advance-cong fields (advance-cong pars (λ j → ≈-refl {t = tm-var j})) k

    result-arity : ∀ {ps ps′ fields fields′}
      → All2 _≈_ ps ps′ → All2 _≈_ fields fields′
      → length ps ≡ length ps′ × length fields ≡ length fields′
    result-arity pars fields = all2-length pars , all2-length fields

    instantiateResult-cong : ∀ {ps ps′ fields fields′}
      → All2 _≈_ ps ps′ → All2 _≈_ fields fields′
      → ∀ T → F.instantiateResult ps fields T ≈ F.instantiateResult ps′ fields′ T
    instantiateResult-cong {ps} {ps′} {fields} {fields′} pars args T =
      ≈-subst-cong {t = T}
        {σ = F.advance fields (F.advance ps F.identity)}
        {σ′ = F.advance fields′ (F.advance ps′ F.identity)}
        (result-frame-cong pars args)

    instantiateResults-cong : ∀ {ps ps′ fields fields′}
      → All2 _≈_ ps ps′ → All2 _≈_ fields fields′
      → ∀ Ts → All2 _≈_ (F.instantiateResults ps fields Ts)
        (F.instantiateResults ps′ fields′ Ts)
    instantiateResults-cong pars args [] = a2[]
    instantiateResults-cong pars args (T ∷ Ts) =
      a2∷ (instantiateResult-cong pars args T) (instantiateResults-cong pars args Ts)

    spine-locals : ∀ {n} {Γ : Ctx n} {locals locals′ args tele}
      → All2 _≈_ locals locals′ → Spine Γ locals args tele
      → Spine Γ locals′ args tele
    spine-locals equal sp[] = sp[]
    spine-locals equal (sp∷ {arg = arg} {T = T} checked rest) =
      sp∷ (⇐-conv checked (prefix-cong equal T))
        (spine-locals (a2∷ (≈-refl {t = arg}) equal) rest)

    apps-cong : ∀ {f f′ xs ys}
      → f ≈ f′ → All2 _≈_ xs ys → Native.apps f xs ≈ Native.apps f′ ys
    apps-cong equal a2[] = equal
    apps-cong {f} {f′} (equal) (a2∷ {x} {y} arg rest) =
      apps-cong (≈-app {f = f} {f′ = f′} {a = x} {a′ = y} equal arg) rest

    branchGoal-cong : ∀ name ps ctor {m m′} → m ≈ m′
      → Native.branchGoal name ps ctor m ≈ Native.branchGoal name ps ctor m′
    branchGoal-cong name ps ctor {m} {m′} equal =
      apps-cong
        (≈-rename {t = m} {u = m′} (shiftRen (length (ctor-args ctor)) zero) equal)
        (all2-refl
          (map (F.specializeParameters (length (ctor-args ctor)) ps) (ctor-indices ctor)
            ++ tm-ctor name (surface-field-vars (length (ctor-args ctor))) ∷ []))

    branches-motive : ∀ {n} {Γ : Ctx n} {family ps m m′ brs}
      → m ≈ m′ → Branches Γ family ps m brs → Branches Γ family ps m′ brs
    branches-motive equal br[] = br[]
    branches-motive {ps = ps} equal
      (br∷ {name = name} {ctor = ctor} found owner opened wf body rest) =
      br∷ found owner opened wf
        (⇐-conv body (branchGoal-cong name ps ctor equal))
        (branches-motive equal rest)
