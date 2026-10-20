------------------------------------------------------------------------
-- Native root preservation with registry-valued substitution images and
-- a nonempty typed global table over a genuinely dependent registry.
-- No closed-base typing instance is used to certify these derivations.
------------------------------------------------------------------------
module Proof.DependentRootExamples where

open import Data.Bool using (true)
open import Data.Nat using (s≤s; z≤n)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as Fin
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l≤-refl)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Signature
open import Core.Reduction
import Core.DependentTyping as Native
import Proof.DependentTypingExamples as E
import Proof.DependentCoherenceExamples as Frames
import Proof.DependentTransportExamples as TransportExamples
import Proof.DependentRootPreservation as Root
import Proof.ReductionConversion as Reduction
open import Proof.Progress using (f-ctor; f-lam; f-var; f-atom_type)

module P = Root.Roots E.env E.sig E.conv
module V = P.Valid E.valid
module SubstitutionExamples where
  open E.T

  beta-registry-capture : P.Preserved ⟨⟩
    (tm-app (tm-lam unrestricted E.goal
      (tm-lam unrestricted tm-atom_type (tm-var 1))) E.value)
    (tm-lam unrestricted tm-atom_type E.value) (tm-pi unrestricted tm-atom_type E.goal)
  beta-registry-capture = V.beta-at E.goal-kind
    (E.check TransportExamples.native-capture-source) (tt , tt)
    (E.value-typed , (tt , tt) , tt , tt , tt , tt)
    (Conversion.≈-refl E.conv {t = tm-pi unrestricted tm-atom_type E.goal})

  beta-own-binder : P.Preserved ⟨⟩
    (tm-app (tm-lam unrestricted E.goal
      (tm-lam unrestricted tm-atom_type (tm-var 0))) E.value)
    (tm-lam unrestricted tm-atom_type (tm-var 0))
    (tm-pi unrestricted tm-atom_type tm-atom_type)
  beta-own-binder = V.beta-at E.goal-kind
    (⇐-lam ⇒-atom_type (E.check (⇒-var Fin.zero))) (tt , tt)
    (E.value-typed , (tt , tt) , tt , tt , tt , tt)
    (Conversion.≈-refl E.conv {t = tm-pi unrestricted tm-atom_type tm-atom_type})

  zeta-registry-capture : P.Preserved ⟨⟩
    (tm-let unrestricted E.goal E.value (tm-lam unrestricted tm-atom_type (tm-var 1)))
    (tm-lam unrestricted tm-atom_type E.value) (tm-pi unrestricted tm-atom_type E.goal)
  zeta-registry-capture = V.zeta-at E.goal-kind
    (E.check E.value-typed) ((tt , tt) , tt , tt , tt , tt) (f-ctor Frames.fields-final)
    TransportExamples.native-capture-source (tt , tt)
    (Conversion.≈-refl E.conv {t = tm-pi unrestricted tm-atom_type E.goal})

  identity-type identity-term : Term
  identity-type = tm-pi unrestricted tm-atom_type tm-atom_type
  identity-term = tm-lam unrestricted tm-atom_type (tm-var 0)
  zeta-checked-lambda : P.Preserved ⟨⟩
    (tm-let unrestricted identity-type identity-term (tm-app (tm-var 0) (tm-atom_lit "payload")))
    (tm-app identity-term (tm-atom_lit "payload")) tm-atom_type
  zeta-checked-lambda = V.zeta-at (⇒-pi ⇒-atom_type ⇒-atom_type)
    (⇐-lam ⇒-atom_type (E.check (⇒-var Fin.zero))) (tt , tt) (f-lam f-atom_type f-var)
    (⇒-app (⇒-var Fin.zero) ⇒-atom_lit) (tt , tt)
    (Conversion.≈-refl E.conv {t = tm-atom_type})

module Globals where
  -- NativeRoot(A : Type0; x : A), with one uniform constructor.
  ps tele : Telescope
  ps = ("A" , tm-type l0) ∷ []
  tele = ("x" , tm-var 0) ∷ []
  ctor : Ctor
  ctor = record
    { ctor-name = "NativeRootMk" ; ctor-args = tele
    ; ctor-params = tm-var 1 ∷ [] ; ctor-indices = tm-var 0 ∷ [] }
  family : Family
  family = record
    { fam-name = "NativeRoot" ; fam-params = ps ; fam-indices = tele
    ; fam-level = l0 ; fam-ctors = ctor ∷ [] ; positive = true ; universe-ok = true }
  env : IndEnv
  env = record { families = family ∷ [] ; builtins = λ _ → nothing }
  goal value declared-type : Term
  goal = tm-data "NativeRoot" (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ [])
  value = tm-ctor "NativeRootMk" (tm-atom_lit "payload" ∷ [])
  declared-type = tm-let unrestricted tm-atom_type (tm-atom_lit "ignored") goal
  types bodies : Name → Maybe Term
  types name with name ≟ "native-root"
  ... | yes equal = just declared-type
  ... | no different = nothing
  bodies name with name ≟ "native-root"
  ... | yes equal = just value
  ... | no different = nothing
  sig : Signature
  sig = record { type-of = types ; body = bodies }
  value-scoped : Scoped 0 value
  value-scoped = sc-ctor (st∷ sc-atom_lit st[])
  body-closed : ∀ {name b} → bodies name ≡ just b → Scoped 0 b
  body-closed {name} found with name ≟ "native-root"
  ... | yes equal with just-inj found
  ... | refl = value-scoped
  body-closed {name} () | no different
  module R = Reduction.Model sig body-closed
  conv : Conversion
  conv = R.conversion
  module N = Native.Typing env sig conv

  -- A separate native namespace prevents any old E judgment being used
  -- as a declaration/body typing witness for this signature.
  module Witnesses where
    open N
    check : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Γ ⊢ t ⇐ T
    check {T = T} typed = ⇐-infer typed (Conversion.≈-refl conv {t = T})
    Π : Ctx 1
    Π = extend ⟨⟩ (tm-type l0)
    Φ : Ctx 2
    Φ = extend Π (tm-var 0)
    parameters : Declared ⟨⟩ ps Π
    parameters = dt∷ sc-type (⇒-type refl) dt[]
    fields : Declared Π tele Φ
    fields = dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[]
    family-declaration : FamilyDeclaration family
    family-declaration = record
      { parameter-context = Π ; index-context = Φ ; parameters = parameters ; indices = fields }
    ctor-declaration : ConstructorDeclaration family ctor
    ctor-declaration = record
      { parameter-context = Π ; field-context = Φ ; parameters = parameters ; fields = fields
      ; field-levels = l≤-refl , tt ; uniform-parameters = refl
      ; result-scoping = st∷ (sc-var (s≤s (s≤s z≤n))) st[] , st∷ (sc-var (s≤s z≤n)) st[]
      ; result-parameters = sp∷ (check (⇒-var (Fin.suc Fin.zero))) sp[]
      ; result-indices = sp∷ (check (⇒-var Fin.zero)) sp[] }
    pa : Spine ⟨⟩ [] (tm-atom_type ∷ []) ps
    pa = sp∷ (check ⇒-atom_type) sp[]
    fa : Spine ⟨⟩ (tm-atom_type ∷ []) (tm-atom_lit "payload" ∷ []) tele
    fa = sp∷ (check ⇒-atom_lit) sp[]
    goal-kind : ⟨⟩ ⊢ goal ⇒ tm-type l0
    goal-kind = ⇒-data refl pa fa
    value-typed : ⟨⟩ ⊢ value ⇒ declared-type
    value-typed = ⇒-conv (⇒-ctor refl pa fa)
      (Conversion.≈-sym conv {t = declared-type} {u = goal}
        (R.reduce-converts {t = declared-type} {u = goal} ζ))
    declared-scoped : Scoped 0 declared-type
    declared-scoped = sc-let sc-atom_type sc-atom_lit
      (sc-data (st∷ sc-atom_type st[]) (st∷ sc-atom_lit st[]))
    declared-kind : ⟨⟩ ⊢ declared-type ⇒ tm-type l0
    declared-kind = ⇒-let ⇒-atom_type (check ⇒-atom_lit)
      (⇒-data refl (sp∷ (check ⇒-atom_type) sp[]) (sp∷ (check ⇒-atom_lit) sp[]))
    family-valid : ∀ {name f}
      → findFamily name (IndEnv.families env) ≡ just f → FamilyDeclaration f
    family-valid {name} found with name ≟ "NativeRoot"
    ... | yes refl with just-inj found
    ... | refl = family-declaration
    family-valid {name} () | no different
    ctor-valid : ∀ {name f ct}
      → findCtor name (IndEnv.families env) ≡ just (f , ct) → ConstructorDeclaration f ct
    ctor-valid {name} found with name ≟ "NativeRootMk"
    ... | yes refl with just-inj found
    ... | refl = ctor-declaration
    ctor-valid {name} () | no different
    owner-visible : ∀ {name f ct}
      → findCtor name (IndEnv.families env) ≡ just (f , ct)
      → findFamily (fam-name f) (IndEnv.families env) ≡ just f
    owner-visible {name} found with name ≟ "NativeRootMk"
    ... | yes refl with just-inj found
    ... | refl = refl
    owner-visible {name} () | no different
    global-type-valid : ∀ {name T} → types name ≡ just T
      → Scoped 0 T × (Data.Product.∃ λ l → ⟨⟩ ⊢ T ⇒ tm-type l)
    global-type-valid {name} found with name ≟ "native-root"
    ... | yes equal with just-inj found
    ... | refl = declared-scoped , l0 , declared-kind
    global-type-valid {name} () | no different
    global-body-valid : ∀ {name b} → bodies name ≡ just b
      → Data.Product.∃ λ T → types name ≡ just T × Scoped 0 b × (⟨⟩ ⊢ b ⇒ T)
    global-body-valid {name} found with name ≟ "native-root"
    ... | yes refl with just-inj found
    ... | refl = declared-type , refl , value-scoped , value-typed
    global-body-valid {name} () | no different
    valid : SignatureValid
    valid = record
      { family-declared = λ {name} → family-valid {name}
      ; constructor-declared = λ {name} → ctor-valid {name}
      ; owner-visible = λ {name} → owner-visible {name}
      ; global-type = λ {name} → global-type-valid {name}
      ; global-body = λ {name} → global-body-valid {name} }

  module Roots = Root.Roots env sig conv
  module Valid = Roots.Valid Witnesses.valid
  delta-native : ∀ {n} {Γ : Ctx n} → Roots.Preserved Γ (tm-global "native-root") value goal
  delta-native = Valid.delta-at {name = "native-root"} refl
    ((tt , tt) , tt , tt) (R.reduce-converts {t = declared-type} {u = goal} ζ)

  delta-declared-goal : ∀ {n} {Γ : Ctx n}
    → Roots.Preserved Γ (tm-global "native-root") value declared-type
  delta-declared-goal = Valid.delta-at {name = "native-root"} refl
    ((tt , tt) , tt , tt) (Conversion.≈-refl conv {t = declared-type})

  unknown-body-not-unfolded : ∀ {t} → _⇝_ sig (tm-global "unknown") t → ⊥
  unknown-body-not-unfolded (δ ())
  unknown-global-not-typed : ∀ {n} {Γ : Ctx n} {T}
    → N._⊢_⇒_ Γ (tm-global "unknown") T → ⊥
  unknown-global-not-typed (N.⇒-global ())
  unknown-global-not-typed (N.⇒-conv typed equal) = unknown-global-not-typed typed
  unknown-global-not-typed (N.⇒-cumul typed le) = unknown-global-not-typed typed
