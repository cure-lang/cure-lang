{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- A migration boundary, NOT a contradiction in the closed-entry theorem.
-- Adding a registry-only scrutinee to a BASE context gives no base family
-- coverage obligations. A base sort derivation is not thereby a checked
-- motive certificate for the registered extension. Closing that context
-- with its actual registered ctor is not a coherent BASE substitution.
------------------------------------------------------------------------
module Proof.MotiveBoundaryAudit where

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1)
open import Core.Signature using (IndEnv; fam-name; ctor-args; findCtor)
open import Core.Coverage
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; extend)
open import Proof.Progress using (Final; f-case; f-var; f-lam; f-atom_type; f-type; fb[])
import Proof.SoundnessModel as M
import Proof.DependentRegistryExamples as G

open Core.Typing.Typing M.env M.sig M.conv

extension-type actual-constructor : Term
extension-type = tm-data "LocalResult" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
actual-constructor = tm-ctor "LocalMk" (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
Γ : Ctx 1
Γ = extend ⟨⟩ extension-type

base-constructor-coverage : ∀ {name family ctor}
  → findCtor name (IndEnv.families M.env) ≡ just (family , ctor)
  → fam-name family ≡ "LocalResult" → HasBranch name (length (ctor-args ctor)) []
base-constructor-coverage {name} found owner
  with lookup-ctor-members {c = name} {fs = IndEnv.families M.env} found
base-constructor-coverage found () | here refl , member , equal
base-constructor-coverage found () | there (here refl) , member , equal
base-constructor-coverage found owner | there (there ()) , member , equal

vacuous-in-base : CaseCoverage M.env "LocalResult" []
vacuous-in-base = record
  { ctor-covered = λ {name} → base-constructor-coverage {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }
-- Coverage must be recomputed in the environment that admits the scrutinee.
-- The same empty branches cannot cover the genuinely inhabited registry.
registry-empty-coverage-rejected : CaseCoverage G.registry "LocalResult" [] → ⊥
registry-empty-coverage-rejected covered
  with ctor-covered covered {c = "LocalMk"} refl refl
... | body , ()

base-coverage-not-registry-stable :
  (CaseCoverage M.env "LocalResult" [] → CaseCoverage G.registry "LocalResult" []) → ⊥
base-coverage-not-registry-stable transfer =
  registry-empty-coverage-rejected (transfer vacuous-in-base)

-- The old rule infers a motive but applies it to the scrutinee ONLY. It
-- does not validate the extension's curried index/scrutinee contract.
unary-motive audit-body : Term
unary-motive = tm-lam unrestricted tm-atom_type (tm-type l0)
audit-body = tm-case (tm-var 0) unary-motive []
unary-infers : Γ ⊢ unary-motive ⇒ tm-pi unrestricted tm-atom_type (tm-type l1)
unary-infers = ⇒-lam ⇒-atom_type (⇐-infer (⇒-type refl) (M.eq-refl {tm-type l1}))
base-body-sort : Γ ⊢ audit-body ⇒ tm-type l0
base-body-sort = ⇒-conv (⇒-case (⇒-var Fin.zero) unary-infers brs[] vacuous-in-base)
  (M.rc {t = tm-app unary-motive (tm-var 0)} {t′ = tm-type l0} β)
base-body-final : Final audit-body
base-body-final = f-case f-var (f-lam f-atom_type f-type) fb[]

-- The registry DOES contain an admitted ctor and its checked result.
registered-application : G.L.Application ⟨⟩ "LocalMk" (tm-atom_type ∷ [])
  (tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ [])
registered-application = G.application

constructor-not-base-typed : ∀ {n} {Δ : Ctx n} {T} → Δ ⊢ actual-constructor ⇒ T → ⊥
constructor-not-base-typed (⇒-ctor () arguments)
constructor-not-base-typed (⇒-conv der equal) = constructor-not-base-typed der
constructor-not-base-typed (⇒-cumul der le) = constructor-not-base-typed der

closing-not-base-coherent : M.P.Coherent Γ ⟨⟩ (topSub actual-constructor) → ⊥
closing-not-base-coherent coherent = constructor-not-base-typed (coherent Fin.zero)

closed-body : Term
closed-body = substTopT actual-constructor audit-body
closed-body-not-base-typed : ∀ {T} → ⟨⟩ ⊢ closed-body ⇒ T → ⊥
closed-body-not-base-typed (⇒-case scrutinee motive branches coverage) =
  constructor-not-base-typed scrutinee
closed-body-not-base-typed (⇒-conv der equal) = closed-body-not-base-typed der
closed-body-not-base-typed (⇒-cumul der le) = closed-body-not-base-typed der
