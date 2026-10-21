{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Typed forward-dependent spine witnesses, NOT a migration of the main
-- constructor/branch rules. The legacy soundness model remains intact.
------------------------------------------------------------------------
module Proof.DependentSpineExamples where

open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l2)
open import Core.Syntax
open import Core.Signature using (Telescope; Ctor)
open import Core.Typing using (Ctx; Conversion; ⟨⟩; extend; lookup-extend; _∈Tele_; ∈-here; ∈-there)
open import Core.TypeHeads using (ty-float; ty-atom; ty-universe)
import Core.LocalFrame as F
import Core.Verification as V
import Proof.DependentSpine as Dependent
import Proof.SoundnessModel as M

open Core.Typing.Typing M.env M.sig M.conv
module D = Dependent.Spines M.env M.sig M.conv
open D using (Checked; ds[]; ds∷)
module S = D.Stability M.closed-signature M.rc M.typed-bodies M.builtin-ctors M.bodies-final

dependent-tele : Telescope
dependent-tele = ("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ []

typed-dependent-fields :
  Checked ⟨⟩ [] (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) dependent-tele
typed-dependent-fields =
  ds∷ sc-type (⇒-type refl) (⇐-infer ⇒-atom_type (M.eq-refl {tm-type l0}))
    (ds∷ (sc-var (s≤s z≤n)) ⇒-atom_type
      (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type})) ds[])

-- The second declaration is OPEN in its local frame, but instantiates to
-- Atom before checking x; treating it as a closed raw type is incorrect.
dependent-entry-not-closed : Scoped 0 (tm-var 0) → ⊥
dependent-entry-not-closed (sc-var ())

float-at-atom : ∀ {n} {Γ : Ctx n} {T}
  → Γ ⊢ tm-float_lit ⇒ T → Conversion._≈_ M.conv T tm-atom_type → ⊥
float-at-atom ⇒-float_lit eq with Conversion.≈-heads M.conv ty-float ty-atom eq
... | ()
float-at-atom (⇒-conv {T = T} {T′ = T′} der eq′) eq =
  float-at-atom der
    (Conversion.≈-trans M.conv {t = T} {u = T′} {v = tm-atom_type} eq′ eq)
float-at-atom (⇒-cumul der le) eq with Conversion.≈-heads M.conv ty-universe ty-atom eq
... | ()

bad-dependent-value-rejected :
  Checked ⟨⟩ [] (tm-atom_type ∷ tm-float_lit ∷ []) dependent-tele → ⊥
bad-dependent-value-rejected (ds∷ scoped kind arg (ds∷ scoped′ kind′ bad rest)) =
  float-at-atom (M.P.check-infer (λ name ()) bad) (M.eq-refl {tm-atom_type})

ceiling-not-inferable : ∀ {n} {Γ : Ctx n} {T} → Γ ⊢ tm-type l2 ⇒ T → ⊥
ceiling-not-inferable (⇒-type ())
ceiling-not-inferable (⇒-conv der eq) = ceiling-not-inferable der
ceiling-not-inferable (⇒-cumul der le) = ceiling-not-inferable der

bad-entry-kind-rejected :
  Checked ⟨⟩ [] (tm-type l1 ∷ []) (("x" , tm-type l2) ∷ []) → ⊥
bad-entry-kind-rejected (ds∷ scoped kind arg rest) = ceiling-not-inferable kind

-- An argument can check at Type2 although Type2 has no kind in the fixed
-- hierarchy. Entry scoping alone is therefore not declaration validity.
flat-rule-has-no-kind-premise : ⟨⟩ ⊢* (tm-type l1 ∷ []) ⇐* (("x" , tm-type l2) ∷ [])
flat-rule-has-no-kind-premise = ⊢*∷
  (⇐-infer (⇒-type refl) (M.eq-refl {tm-type l2})) ⊢*[]

second-expected-type : F.instantiatePrefix (tm-atom_type ∷ []) (tm-var 0) ≡ tm-atom_type
second-expected-type = refl

dependent-result-index :
  F.instantiateResult [] (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) (tm-var 1) ≡ tm-atom_type
dependent-result-index = refl

last-dependent-field :
  F.instantiateFields (tm-atom_type ∷ tm-atom_lit "payload" ∷ []) (tm-var 0)
    ≡ tm-atom_lit "payload"
last-dependent-field = refl

-- A constructor telescope may start with a parameter frame. Parameters
-- are NOT branch fields and must remain in result-index instantiation.
parameter-field :
  Checked ⟨⟩ (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
    (("x" , tm-var 0) ∷ [])
parameter-field =
  ds∷ (sc-var (s≤s z≤n)) ⇒-atom_type
    (⇐-infer ⇒-atom_lit (M.eq-refl {tm-atom_type})) ds[]

parameter-in-result :
  F.instantiateResult (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ []) (tm-var 1) ≡ tm-atom_type
parameter-in-result = refl

parameter-ctor : Ctor
parameter-ctor = record
  { ctor-name = "Seeded" ; ctor-args = ("x" , tm-var 0) ∷ []
  ; ctor-params = tm-var 1 ∷ [] ; ctor-indices = tm-var 0 ∷ [] }

parameter-vector :
  V.instantiateParameters parameter-ctor (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
    ≡ tm-atom_type ∷ []
parameter-vector = refl

index-vector :
  V.instantiateIndicesWithParameters parameter-ctor
    (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
    ≡ tm-atom_lit "payload" ∷ []
index-vector = refl

parameter-is-not-a-branch-field :
  F.instantiateFields (tm-atom_lit "payload" ∷ []) (tm-var 1) ≡ tm-var 0
parameter-is-not-a-branch-field = refl

-- Entry kinding, exact arity and preceding-binder scope are real premises.
forward-reference-rejected : ∀ {arg}
  → Checked ⟨⟩ [] (arg ∷ []) (("x" , tm-var 0) ∷ []) → ⊥
forward-reference-rejected (ds∷ (sc-var ()) kind arg rest)

missing-field-rejected : Checked ⟨⟩ [] [] dependent-tele → ⊥
missing-field-rejected ()
extra-field-rejected : ∀ {arg} → Checked ⟨⟩ [] (arg ∷ []) [] → ⊥
extra-field-rejected ()

-- Open caller variables are transported, not captured by the local frame.
Γ : Ctx 1
Γ = extend ⟨⟩ tm-atom_type
Δ : Ctx 2
Δ = extend Γ tm-atom_type

open-field : Checked Γ [] (tm-var 0 ∷ []) (("x" , tm-atom_type) ∷ [])
open-field = ds∷ sc-atom_type ⇒-atom_type
  (⇐-infer (⇒-var Fin.zero) (M.eq-refl {tm-atom_type})) ds[]

renamed-open-field : Checked Δ [] (tm-var 1 ∷ []) (("x" , tm-atom_type) ∷ [])
renamed-open-field =
  S.rename-checked {Γ = Γ} {Δ = Δ} {ρ = wk} Fin.suc (λ i → refl)
    (lookup-extend Γ tm-atom_type) open-field

coherent : S.P.Coherent Γ ⟨⟩ (topSub (tm-atom_lit "payload"))
coherent Fin.zero = ⇒-atom_lit
coherent (Fin.suc ())

substituted-open-field :
  Checked ⟨⟩ [] (tm-atom_lit "payload" ∷ []) (("x" , tm-atom_type) ∷ [])
substituted-open-field = S.subst-checked {Γ = Γ} {Δ = ⟨⟩}
  {σ = topSub (tm-atom_lit "payload")} coherent open-field

-- Whole-term frame regression: an inserted OPEN field is shifted under
-- a lambda, while that lambda's own variable remains bound.
no-capture-under-lambda :
  F.instantiateFields (tm-var 0 ∷ tm-var 1 ∷ [])
    (tm-lam unrestricted tm-atom_type (tm-app (tm-var 1) (tm-var 0)))
  ≡ tm-lam unrestricted tm-atom_type (tm-app (tm-var 2) (tm-var 0))
no-capture-under-lambda = refl

nested-branch-keeps-own-field :
  F.instantiateFields (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
    (tm-case (tm-var 0) tm-atom_type
      (("Inner" , 1 , tm-ctor "Pair" (tm-var 0 ∷ tm-var 1 ∷ [])) ∷ []))
  ≡ tm-case (tm-atom_lit "payload") tm-atom_type
      (("Inner" , 1 , tm-ctor "Pair" (tm-var 0 ∷ tm-atom_lit "payload" ∷ [])) ∷ [])
nested-branch-keeps-own-field = refl

-- The new judgment can supply the ACTIVE rule for a closed telescope.
closed-nat-field : Checked ⟨⟩ [] (tm-nat_lit 7 ∷ []) (("_" , M.N) ∷ [])
closed-nat-field =
  ds∷ (sc-data st[] st[]) M.nat-kind
    (⇐-infer (⇒-nat_lit refl) (M.eq-refl {M.N})) ds[]

closed-field : ∀ {T} → T ∈Tele (("_" , M.N) ∷ []) → Scoped 0 T
closed-field ∈-here = sc-data st[] st[]
closed-field (∈-there ())

active-constructor-typed : ⟨⟩ ⊢ tm-ctor "S" (tm-nat_lit 7 ∷ []) ⇒ M.N
active-constructor-typed = ⇒-ctor refl (D.closed-to-flat closed-field closed-nat-field)
