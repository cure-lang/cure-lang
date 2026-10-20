------------------------------------------------------------------------
-- One native declaration/conversion model with real dependent globals
-- and compact literal layouts. Finality does not assert termination.
------------------------------------------------------------------------
module Proof.DependentSoundnessModel where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit using (tt)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l≤-refl; l0≤l1)
open import Core.Signature
open import Core.Reduction
open import Core.Coverage
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.DependentTyping
import Core.LocalFrame as F
import Proof.ReductionConversion as Reduction
import Proof.DependentDataConversion as Data
import Proof.DependentLiteralPreservation as Literal
open import Proof.Substitution using (subst-extSub-wk; topSub-rename)
open import Proof.Progress using
  (Final; FinalTerms; FinalBranches; BodiesFinal; f-type; f-var; f-lam;
   f-let; f-case; f-data; f-ctor; f-global; f-atom_type; f-atom_lit;
   f-float_type; f-float_lit; f-nat_lit; f-bounded_lit; ft[]; ft∷; fb[]; fb∷)

parameters indices : Telescope
parameters = ("A" , tm-type l0) ∷ []
indices = ("x" , tm-var 0) ∷ ("B" , tm-type l0) ∷ ("y" , tm-var 0) ∷ []
computed-index : Term
computed-index = tm-app (tm-lam unrestricted (tm-var 3) (tm-var 0)) (tm-var 2)
mk computed : Ctor
mk = record
  { ctor-name = "NativeMk"; ctor-args = indices; ctor-params = tm-var 3 ∷ []
  ; ctor-indices = tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ [] }
computed = record mk
  { ctor-name = "NativeComputed"
  ; ctor-indices = computed-index ∷ tm-var 1 ∷ tm-var 0 ∷ [] }
family : Family
family = record
  { fam-name = "NativeD"; fam-params = parameters; fam-indices = indices
  ; fam-level = l1; fam-ctors = mk ∷ computed ∷ []
  ; positive = true; universe-ok = true }
zero suc first next : Ctor
zero = record
  { ctor-name = "Z"; ctor-args = []; ctor-params = []; ctor-indices = [] }
suc = record
  { ctor-name = "S"; ctor-args = ("predecessor" , tm-data "LiteralNat" [] []) ∷ []
  ; ctor-params = []; ctor-indices = [] }
first = record
  { ctor-name = "First"; ctor-args = ("initial-bound" , tm-data "LiteralNat" [] []) ∷ []
  ; ctor-params = []; ctor-indices = [] }
next = record
  { ctor-name = "Next"
  ; ctor-args = ("bound" , tm-data "LiteralNat" [] []) ∷
      ("previous" , tm-data "LiteralBounded" [] []) ∷ []
  ; ctor-params = []; ctor-indices = [] }
nat bounded : Family
nat = record
  { fam-name = "LiteralNat"; fam-params = []; fam-indices = []; fam-level = l0
  ; fam-ctors = zero ∷ suc ∷ []; positive = true; universe-ok = true }
bounded = record
  { fam-name = "LiteralBounded"; fam-params = []; fam-indices = []; fam-level = l0
  ; fam-ctors = first ∷ next ∷ []; positive = true; universe-ok = true }
identities : Name → Maybe Name
identities key with key ≟ "nat"
... | yes same = just "LiteralNat"
... | no different with key ≟ "bounded"
... | yes same = just "LiteralBounded"
... | no different = nothing
env : IndEnv
env = record { families = family ∷ nat ∷ bounded ∷ []; builtins = identities }

fields : List Term
fields = tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []
computed-results : List Term
computed-results = F.instantiateResults (tm-atom_type ∷ []) fields (ctor-indices computed)
goal value declared-type : Term
goal = tm-data "NativeD" (tm-atom_type ∷ []) computed-results
value = tm-ctor "NativeComputed" fields
declared-type = tm-let unrestricted tm-atom_type (tm-atom_lit "ignored") goal
types bodies : Name → Maybe Term
types name with name ≟ "native-dependent"
... | yes equal = just declared-type
... | no different = nothing
bodies name with name ≟ "native-dependent"
... | yes equal = just value
... | no different = nothing
sig : Signature
sig = record { body = bodies; type-of = types }
global-body-found : Signature.body sig "native-dependent" ≡ just value
global-body-found = refl
global-type-found : Signature.type-of sig "native-dependent" ≡ just declared-type
global-type-found = refl
fields-scoped : ∀ {n} → ScopedTerms n fields
fields-scoped = st∷ sc-atom_lit (st∷ sc-float_type (st∷ sc-float_lit st[]))
value-scoped : Scoped 0 value
value-scoped = sc-ctor fields-scoped
body-closed : ∀ {name b} → bodies name ≡ just b → Scoped 0 b
body-closed {name} found with name ≟ "native-dependent"
... | yes equal with just-inj found
... | refl = value-scoped
body-closed {name} () | no different
module R = Reduction.Model sig body-closed
conv : Conversion
conv = R.conversion
module D = Data.Model sig body-closed
module N = Core.DependentTyping.Typing env sig conv
module T = N
open N
open Conversion
check : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ⇒ A → Γ ⊢ t ⇐ A
check {A = A} der = ⇐-infer der (≈-refl conv {t = A})

Π : Ctx 1
Π = extend ⟨⟩ (tm-type l0)
Φ : Ctx 4
Φ = extend (extend (extend Π (tm-var 0)) (tm-type l0)) (tm-var 0)
parameters-declared : Declared ⟨⟩ parameters Π
parameters-declared = dt∷ sc-type (⇒-type refl) dt[]
indices-declared : Declared Π indices Φ
indices-declared = dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero)
  (dt∷ sc-type (⇒-type refl)
    (dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[]))
local-parameters : Spine Φ [] (ctor-params mk) parameters
local-parameters = sp∷ (check (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) sp[]
local-indices : Spine Φ (tm-var 3 ∷ []) (ctor-indices mk) indices
local-indices = sp∷ (check (⇒-var (Fin.suc (Fin.suc Fin.zero))))
  (sp∷ (check (⇒-var (Fin.suc Fin.zero))) (sp∷ (check (⇒-var Fin.zero)) sp[]))
local-computed : Φ ⊢ computed-index ⇒ tm-var 3
local-computed = ⇒-app
  (⇒-lam {c = tm-var 4} (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
    (check (⇒-var Fin.zero))) (⇒-var (Fin.suc (Fin.suc Fin.zero)))
family-declaration : FamilyDeclaration family
family-declaration = record
  { parameter-context = Π; index-context = Φ
  ; parameters = parameters-declared; indices = indices-declared }
mk-declaration : ConstructorDeclaration family mk
mk-declaration = record
  { parameter-context = Π; field-context = Φ
  ; parameters = parameters-declared; fields = indices-declared
  ; field-levels = l0≤l1 , l≤-refl , l0≤l1 , tt
  ; result-scoping = st∷ (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) st[] ,
      st∷ (sc-var (s≤s (s≤s (s≤s z≤n))))
        (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[]))
  ; uniform-parameters = refl
  ; result-parameters = local-parameters; result-indices = local-indices }
computed-declaration : ConstructorDeclaration family computed
computed-declaration = record
  { parameter-context = Π; field-context = Φ
  ; parameters = parameters-declared; fields = indices-declared
  ; field-levels = l0≤l1 , l≤-refl , l0≤l1 , tt
  ; result-scoping = st∷ (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) st[] ,
      st∷ (sc-app (sc-lam (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) (sc-var (s≤s z≤n)))
        (sc-var (s≤s (s≤s (s≤s z≤n)))))
        (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[]))
  ; uniform-parameters = refl; result-parameters = local-parameters
  ; result-indices = sp∷ (check local-computed)
      (sp∷ (check (⇒-var (Fin.suc Fin.zero))) (sp∷ (check (⇒-var Fin.zero)) sp[])) }
nat-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-data "LiteralNat" [] [] ⇒ tm-type l0
nat-kind = ⇒-data refl sp[] sp[]
bounded-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-data "LiteralBounded" [] [] ⇒ tm-type l0
bounded-kind = ⇒-data refl sp[] sp[]
nat-scoped : ∀ {n} → Scoped n (tm-data "LiteralNat" [] [])
nat-scoped = sc-data st[] st[]
bounded-scoped : ∀ {n} → Scoped n (tm-data "LiteralBounded" [] [])
bounded-scoped = sc-data st[] st[]
nat-declaration : FamilyDeclaration nat
nat-declaration = record
  { parameter-context = ⟨⟩; index-context = ⟨⟩; parameters = dt[]; indices = dt[] }
bounded-declaration : FamilyDeclaration bounded
bounded-declaration = record
  { parameter-context = ⟨⟩; index-context = ⟨⟩; parameters = dt[]; indices = dt[] }
zero-declaration : ConstructorDeclaration nat zero
zero-declaration = record
  { parameter-context = ⟨⟩; field-context = ⟨⟩; parameters = dt[]; fields = dt[]
  ; field-levels = tt; result-scoping = st[] , st[]; uniform-parameters = refl
  ; result-parameters = sp[]; result-indices = sp[] }
suc-declaration : ConstructorDeclaration nat suc
suc-declaration = record
  { parameter-context = ⟨⟩; field-context = extend ⟨⟩ (tm-data "LiteralNat" [] [])
  ; parameters = dt[]; fields = dt∷ nat-scoped nat-kind dt[]
  ; field-levels = l≤-refl , tt; result-scoping = st[] , st[]; uniform-parameters = refl
  ; result-parameters = sp[]; result-indices = sp[] }
first-declaration : ConstructorDeclaration bounded first
first-declaration = record
  { parameter-context = ⟨⟩; field-context = extend ⟨⟩ (tm-data "LiteralNat" [] [])
  ; parameters = dt[]; fields = dt∷ nat-scoped nat-kind dt[]
  ; field-levels = l≤-refl , tt; result-scoping = st[] , st[]; uniform-parameters = refl
  ; result-parameters = sp[]; result-indices = sp[] }
next-declaration : ConstructorDeclaration bounded next
next-declaration = record
  { parameter-context = ⟨⟩
  ; field-context = extend (extend ⟨⟩ (tm-data "LiteralNat" [] [])) (tm-data "LiteralBounded" [] [])
  ; parameters = dt[]; fields = dt∷ nat-scoped nat-kind (dt∷ bounded-scoped bounded-kind dt[])
  ; field-levels = l≤-refl , l≤-refl , tt; result-scoping = st[] , st[]
  ; uniform-parameters = refl; result-parameters = sp[]; result-indices = sp[] }

actual-parameters : ∀ {n} {Γ : Ctx n} → Spine Γ [] (tm-atom_type ∷ []) parameters
actual-parameters = sp∷ (check ⇒-atom_type) sp[]
actual-fields : ∀ {n} {Γ : Ctx n} → Spine Γ (tm-atom_type ∷ []) fields indices
actual-fields = sp∷ (check ⇒-atom_lit)
  (sp∷ (check ⇒-float_type) (sp∷ (check ⇒-float_lit) sp[]))
actual-results : ∀ {n} {Γ : Ctx n} → Spine Γ (tm-atom_type ∷ []) computed-results indices
actual-results = sp∷ (check (⇒-app
  (⇒-lam ⇒-atom_type (check (⇒-var Fin.zero))) ⇒-atom_lit))
  (sp∷ (check ⇒-float_type) (sp∷ (check ⇒-float_lit) sp[]))
goal-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ goal ⇒ tm-type l1
goal-kind = ⇒-data refl actual-parameters actual-results
goal-scoped : ∀ {n} → Scoped n goal
goal-scoped = sc-data (st∷ sc-atom_type st[])
  (st∷ (sc-app (sc-lam sc-atom_type (sc-var (s≤s z≤n))) sc-atom_lit)
    (st∷ sc-float_type (st∷ sc-float_lit st[])))
value-typed : ∀ {n} {Γ : Ctx n} → Γ ⊢ value ⇒ goal
value-typed = ⇒-ctor refl actual-parameters actual-fields
unwrap : Conversion._≈_ conv declared-type goal
unwrap = R.reduce-converts {t = declared-type} {u = goal} ζ
value-declared : ⟨⟩ ⊢ value ⇒ declared-type
value-declared = ⇒-conv value-typed (≈-sym conv {t = declared-type} {u = goal} unwrap)
declared-scoped : Scoped 0 declared-type
declared-scoped = sc-let sc-atom_type sc-atom_lit goal-scoped
declared-kind : ⟨⟩ ⊢ declared-type ⇒ tm-type l1
declared-kind = ⇒-let ⇒-atom_type (check ⇒-atom_lit) goal-kind

family-valid : ∀ {name f} → findFamily name (IndEnv.families env) ≡ just f → FamilyDeclaration f
family-valid {name} found with name ≟ "NativeD"
... | yes refl with just-inj found
... | refl = family-declaration
family-valid {name} found | no different with name ≟ "LiteralNat"
... | yes refl with just-inj found
... | refl = nat-declaration
family-valid {name} found | no different | no other with name ≟ "LiteralBounded"
... | yes refl with just-inj found
... | refl = bounded-declaration
family-valid {name} () | no different | no other | no remaining
ctor-valid : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → ConstructorDeclaration f ct
ctor-valid {name} found with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , equal = mk-declaration
... | here refl , there (here refl) , equal = computed-declaration
... | here refl , there (there ()) , equal
... | there (here refl) , here refl , equal = zero-declaration
... | there (here refl) , there (here refl) , equal = suc-declaration
... | there (here refl) , there (there ()) , equal
... | there (there (here refl)) , here refl , equal = first-declaration
... | there (there (here refl)) , there (here refl) , equal = next-declaration
... | there (there (here refl)) , there (there ()) , equal
... | there (there (there ())) , member , equal
owner-visible : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct)
  → findFamily (fam-name f) (IndEnv.families env) ≡ just f
owner-visible {name} found with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , member , equal = refl
... | there (here refl) , member , equal = refl
... | there (there (here refl)) , member , equal = refl
... | there (there (there ())) , member , equal
global-type-valid : ∀ {name A} → types name ≡ just A
  → Scoped 0 A × (∃ λ l → ⟨⟩ ⊢ A ⇒ tm-type l)
global-type-valid {name} found with name ≟ "native-dependent"
... | yes equal with just-inj found
... | refl = declared-scoped , l1 , declared-kind
global-type-valid {name} () | no different
global-body-valid : ∀ {name b} → bodies name ≡ just b
  → ∃ λ A → types name ≡ just A × Scoped 0 b × (⟨⟩ ⊢ b ⇒ A)
global-body-valid {name} found with name ≟ "native-dependent"
... | yes refl with just-inj found
... | refl = declared-type , refl , value-scoped , value-declared
global-body-valid {name} () | no different
valid : SignatureValid
valid = record
  { family-declared = λ {name} → family-valid {name}
  ; constructor-declared = λ {name} → ctor-valid {name}
  ; owner-visible = λ {name} → owner-visible {name}
  ; global-type = λ {name} → global-type-valid {name}
  ; global-body = λ {name} → global-body-valid {name} }
fields-final : FinalTerms fields
fields-final = ft∷ f-atom_lit (ft∷ f-float_type (ft∷ f-float_lit ft[]))
bodies-final : BodiesFinal sig
bodies-final {name} found with name ≟ "native-dependent"
... | yes equal with just-inj found
... | refl = f-ctor fields-final
bodies-final {name} () | no different

nat-shape : Literal.NatShape env "LiteralNat" nat
nat-shape = record
  { predecessor = "predecessor"
  ; zero-shape = record { ctor = zero; found = refl; fields = refl; results = refl }
  ; suc-shape = record { ctor = suc; found = refl; fields = refl; results = refl } }
bounded-shape : Literal.BoundedShape env "LiteralBounded" bounded
bounded-shape = record
  { nat-name = "LiteralNat"; nat-family = nat
  ; nat-builtin = refl; nat-found = refl; nat-parameters = refl; nat-indices = refl
  ; bound = "bound"; first-bound = "initial-bound"; predecessor = "previous"
  ; zero-shape = record { ctor = first; found = refl; fields = refl; results = refl }
  ; suc-shape = record { ctor = next; found = refl; fields = refl; results = refl } }
nat-shape-at : ∀ {name f} → identities "nat" ≡ just name
  → findFamily name (IndEnv.families env) ≡ just f
  → fam-params f ≡ [] → fam-indices f ≡ [] → Literal.NatShape env name f
nat-shape-at identity found pars inds with just-inj identity
... | refl with just-inj found
... | refl = nat-shape
bounded-shape-at : ∀ {name f} → identities "bounded" ≡ just name
  → findFamily name (IndEnv.families env) ≡ just f
  → fam-params f ≡ [] → fam-indices f ≡ [] → Literal.BoundedShape env name f
bounded-shape-at identity found pars inds with just-inj identity
... | refl with just-inj found
... | refl = bounded-shape
shapes : Literal.BuiltinShapes env
shapes = record { nat-shape = nat-shape-at; bounded-shape = bounded-shape-at }

Fresh : ∀ {n} → Ctx n → Ctx (3 Data.Nat.+ n)
Fresh Γ = extend (extend (extend Γ tm-atom_type) (tm-type l0)) (tm-var 0)
fresh-opening : ∀ {n} {Γ : Ctx n}
  → Opened Γ (F.advance (tm-atom_type ∷ []) F.identity) indices (Fresh Γ)
fresh-opening = op∷ (op∷ (op∷ op[]))
fresh-wf : ∀ {n} {Γ : Ctx n} → WellFormed Γ → WellFormed (Fresh Γ)
fresh-wf wf = wf∷ (wf∷ (wf∷ wf sc-atom_type ⇒-atom_type) sc-type (⇒-type refl))
  (sc-var (s≤s z≤n)) (⇒-var Fin.zero)
fresh-kind : ∀ {n} {Γ : Ctx n} → Fresh Γ ⊢
  tm-data "NativeD" (tm-atom_type ∷ []) (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []) ⇒ tm-type l1
fresh-kind = ⇒-data refl actual-parameters
  (sp∷ (check (⇒-var (Fin.suc (Fin.suc Fin.zero))))
    (sp∷ (check (⇒-var (Fin.suc Fin.zero))) (sp∷ (check (⇒-var Fin.zero)) sp[])))
scrutinee-domain motive-term : Term
scrutinee-domain = tm-data "NativeD" (tm-atom_type ∷ []) (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ [])
motive-term = tm-lam unrestricted tm-atom_type
  (tm-lam unrestricted (tm-type l0) (tm-lam unrestricted (tm-var 0)
    (tm-lam unrestricted scrutinee-domain (tm-var 2))))
motive-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ motiveType family (tm-atom_type ∷ []) l0 ⇒ tm-type l1
motive-kind = ⇒-pi ⇒-atom_type (⇒-pi (⇒-type refl)
  (⇒-pi (⇒-var Fin.zero) (⇒-pi fresh-kind (⇒-type refl))))
motive-typed : ∀ {n} {Γ : Ctx n} → Γ ⊢ motive-term ⇒ motiveType family (tm-atom_type ∷ []) l0
motive-typed = ⇒-lam ⇒-atom_type (⇐-lam (⇒-type refl)
  (⇐-lam (⇒-var Fin.zero) (⇐-lam fresh-kind (check (⇒-var (Fin.suc (Fin.suc Fin.zero)))))))
scrutinee-scoped : ∀ {n} → Scoped (3 Data.Nat.+ n) scrutinee-domain
scrutinee-scoped = sc-data (st∷ sc-atom_type st[])
  (st∷ (sc-var (s≤s (s≤s (s≤s z≤n))))
    (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[])))
motive-scoped : ∀ {n} → Scoped n motive-term
motive-scoped = sc-lam sc-atom_type
  (sc-lam sc-type (sc-lam (sc-var (s≤s z≤n))
    (sc-lam scrutinee-scoped (sc-var (s≤s (s≤s (s≤s z≤n)))))))
motive-valid : ∀ {n} {Γ : Ctx n} → Motive Γ family (tm-atom_type ∷ []) motive-term l0
motive-valid = motive motive-scoped motive-kind motive-typed
path-converts : ∀ {t u} → _⇝*_ sig t u → _≈_ conv t u
path-converts {t} ⇝*-refl = ≈-refl conv {t = t}
path-converts {t} {u} (⇝*-step {u = v} step rest) =
  ≈-trans conv {t = t} {u = v} {v = u} (R.reduce-converts step) (path-converts rest)
motive-path : ∀ x B y s → _⇝*_ sig
  (apps motive-term (x ∷ B ∷ y ∷ s ∷ []))
  (substTopT s (substS (extSub (topSub y)) (rename wk (rename wk B))))
motive-path x B y s = ⇝*-step (ξ-app₁ (ξ-app₁ (ξ-app₁ β)))
  (⇝*-step (ξ-app₁ (ξ-app₁ β)) (⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)))
motive-cancel : ∀ B y s →
  substTopT s (substS (extSub (topSub y)) (rename wk (rename wk B))) ≡ B
motive-cancel B y s = trans
  (cong (substTopT s) (trans (subst-extSub-wk (topSub y) (rename wk B))
    (cong (rename wk) (topSub-rename y B)))) (topSub-rename s B)
motive-reduces : ∀ x B y s → _≈_ conv (apps motive-term (x ∷ B ∷ y ∷ s ∷ [])) B
motive-reduces x B y s = subst
  (λ u → _≈_ conv (apps motive-term (x ∷ B ∷ y ∷ s ∷ [])) u)
  (motive-cancel B y s) (path-converts (motive-path x B y s))
motive-symmetric : ∀ x B y s → _≈_ conv B (apps motive-term (x ∷ B ∷ y ∷ s ∷ []))
motive-symmetric x B y s = ≈-sym conv
  {t = apps motive-term (x ∷ B ∷ y ∷ s ∷ [])} {u = B} (motive-reduces x B y s)
branches : List Branch
branches = ("NativeMk" , 3 , tm-var 0) ∷ ("NativeComputed" , 3 , tm-var 0) ∷ []
branches-typed : ∀ {n} {Γ : Ctx n} → WellFormed Γ
  → Branches Γ family (tm-atom_type ∷ []) motive-term branches
branches-typed wf = br∷ refl refl fresh-opening (fresh-wf wf)
  (⇐-infer (⇒-var Fin.zero)
    (motive-symmetric (tm-var 2) (tm-var 1) (tm-var 0)
      (tm-ctor "NativeMk" (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ []))))
  (br∷ refl refl fresh-opening (fresh-wf wf)
    (⇐-infer (⇒-var Fin.zero)
      (motive-symmetric
        (F.specializeParameters 3 (tm-atom_type ∷ []) computed-index)
        (tm-var 1) (tm-var 0)
        (tm-ctor "NativeComputed" (tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ [])))) br[])
covered-ctor : ∀ {name f ct} → findCtor name (IndEnv.families env) ≡ just (f , ct)
  → fam-name f ≡ "NativeD" → HasBranch name (length (ctor-args ct)) branches
covered-ctor {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , refl = tm-var 0 , refl
... | here refl , there (here refl) , refl = tm-var 0 , refl
... | here refl , there (there ()) , equal
covered-ctor found () | there (here refl) , member , equal
covered-ctor found () | there (there (here refl)) , member , equal
covered-ctor found owner | there (there (there ())) , member , equal
coverage : CaseCoverage env "NativeD" branches
coverage = record
  { ctor-covered = λ {name} → covered-ctor {name}
  ; nat-zero-covered = λ (); nat-suc-covered = λ ()
  ; bounded-zero-covered = λ (); bounded-suc-covered = λ () }
global : Term
global = tm-global "native-dependent"
global-typed : ∀ {n} {Γ : Ctx n} → Γ ⊢ global ⇒ goal
global-typed = ⇒-conv (⇒-global refl) unwrap
computed-payload : Term
computed-payload = tm-app (tm-lam unrestricted tm-atom_type (tm-var 0)) (tm-atom_lit "payload")
dependent-program unfolded-program : Term
dependent-program = tm-case global motive-term branches
unfolded-program = tm-case value motive-term branches
dependent-source : ∀ {n} {Γ : Ctx n} → WellFormed Γ → Γ ⊢ dependent-program ⇒ tm-float_type
dependent-source wf = ⇒-conv
  (⇒-case wf refl global-typed actual-parameters actual-results motive-valid (branches-typed wf) coverage)
  (motive-reduces computed-payload tm-float_type tm-float_lit global)
dependent-checked : ⟨⟩ ⊢ dependent-program ⇐ tm-float_type
dependent-checked = check (dependent-source wf[])
motive-final : Final motive-term
motive-final = f-lam f-atom_type (f-lam f-type (f-lam f-var
  (f-lam (f-data (ft∷ f-atom_type ft[]) (ft∷ f-var (ft∷ f-var (ft∷ f-var ft[])))) f-var)))
branches-final : FinalBranches branches
branches-final = fb∷ f-var (fb∷ f-var fb[])
dependent-final : Final dependent-program
dependent-final = f-case f-global motive-final branches-final
branch-bound : ∀ n → 1 Data.Nat.≤ n Data.Nat.+ 3
branch-bound Data.Nat.zero = s≤s z≤n
branch-bound (Data.Nat.suc n) = s≤s z≤n
dependent-scoped : ∀ {n} → Scoped n dependent-program
dependent-scoped {n} = sc-case sc-global motive-scoped
  (sb∷ (sbranch (sc-var (branch-bound n))) (sb∷ (sbranch (sc-var (branch-bound n))) sb[]))
dependent-admitted : Admitted ⟨⟩ dependent-program tm-float_type
dependent-admitted = record
  { signature-valid = valid; context-valid = wf[]; term-scoped = dependent-scoped
  ; goal-scoped = sc-float_type; goal-level = l0; goal-kind = ⇒-float_type
  ; checked = dependent-checked }

nat-motive bounded-motive : Term
nat-motive = tm-lam unrestricted (tm-data "LiteralNat" [] []) tm-float_type
bounded-motive = tm-lam unrestricted (tm-data "LiteralBounded" [] []) tm-float_type
nat-motive-valid : Motive ⟨⟩ nat [] nat-motive l0
nat-motive-valid = motive (sc-lam nat-scoped sc-float_type)
  (⇒-pi nat-kind (⇒-type refl)) (⇒-lam nat-kind (check ⇒-float_type))
bounded-motive-valid : Motive ⟨⟩ bounded [] bounded-motive l0
bounded-motive-valid = motive (sc-lam bounded-scoped sc-float_type)
  (⇒-pi bounded-kind (⇒-type refl)) (⇒-lam bounded-kind (check ⇒-float_type))
constant-check : ∀ {n} {Γ : Ctx n} {term domain arg}
  → Γ ⊢ term ⇒ tm-float_type
  → Γ ⊢ term ⇐ tm-app (tm-lam unrestricted domain tm-float_type) arg
constant-check {domain = domain} {arg} typed = ⇐-infer typed
  (≈-sym conv {t = tm-app (tm-lam unrestricted domain tm-float_type) arg} {u = tm-float_type}
    (R.reduce-converts {t = tm-app (tm-lam unrestricted domain tm-float_type) arg} {u = tm-float_type} β))
nat-branches bounded-branches : List Branch
nat-branches = ("Z" , 0 , tm-float_lit) ∷ ("S" , 1 , dependent-program) ∷ []
bounded-branches = ("First" , 1 , tm-float_lit) ∷ ("Next" , 2 , dependent-program) ∷ []
nat-branches-valid : Branches ⟨⟩ nat [] nat-motive nat-branches
nat-branches-valid = br∷ refl refl op[] wf[] (constant-check ⇒-float_lit)
  (br∷ refl refl (op∷ op[]) (wf∷ wf[] nat-scoped nat-kind)
    (constant-check (dependent-source (wf∷ wf[] nat-scoped nat-kind))) br[])
bounded-branches-valid : Branches ⟨⟩ bounded [] bounded-motive bounded-branches
bounded-branches-valid = br∷ refl refl (op∷ op[]) (wf∷ wf[] nat-scoped nat-kind)
  (constant-check ⇒-float_lit)
  (br∷ refl refl (op∷ (op∷ op[]))
    (wf∷ (wf∷ wf[] nat-scoped nat-kind) bounded-scoped bounded-kind)
    (constant-check (dependent-source
      (wf∷ (wf∷ wf[] nat-scoped nat-kind) bounded-scoped bounded-kind))) br[])
nat-covered : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → fam-name f ≡ "LiteralNat"
  → HasBranch name (length (ctor-args ct)) nat-branches
nat-covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
nat-covered found () | here refl , member , equal
... | there (here refl) , here refl , refl = tm-float_lit , refl
... | there (here refl) , there (here refl) , refl = dependent-program , refl
... | there (here refl) , there (there ()) , equal
nat-covered found () | there (there (here refl)) , member , equal
nat-covered found owner | there (there (there ())) , member , equal
bounded-covered : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → fam-name f ≡ "LiteralBounded"
  → HasBranch name (length (ctor-args ct)) bounded-branches
bounded-covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
bounded-covered found () | here refl , member , equal
bounded-covered found () | there (here refl) , member , equal
... | there (there (here refl)) , here refl , refl = tm-float_lit , refl
... | there (there (here refl)) , there (here refl) , refl = dependent-program , refl
... | there (there (here refl)) , there (there ()) , equal
bounded-covered found owner | there (there (there ())) , member , equal
nat-coverage : CaseCoverage env "LiteralNat" nat-branches
nat-coverage = record
  { ctor-covered = λ {name} → nat-covered {name}
  ; nat-zero-covered = λ identity → tm-float_lit , refl
  ; nat-suc-covered = λ identity → dependent-program , refl
  ; bounded-zero-covered = λ (); bounded-suc-covered = λ () }
bounded-coverage : CaseCoverage env "LiteralBounded" bounded-branches
bounded-coverage = record
  { ctor-covered = λ {name} → bounded-covered {name}
  ; nat-zero-covered = λ (); nat-suc-covered = λ ()
  ; bounded-zero-covered = λ identity → tm-float_lit , refl
  ; bounded-suc-covered = λ identity → dependent-program , refl }

program bounded-program : Term
program = tm-case (tm-nat_lit 8) nat-motive nat-branches
bounded-program = tm-case (tm-bounded_lit 8) bounded-motive bounded-branches
program-source : ⟨⟩ ⊢ program ⇒ tm-float_type
program-source = ⇒-conv
  (⇒-case wf[] refl (⇒-nat_lit refl refl refl refl) sp[] sp[]
    nat-motive-valid nat-branches-valid nat-coverage)
  (R.reduce-converts {t = tm-app nat-motive (tm-nat_lit 8)} {u = tm-float_type} β)
bounded-source : ⟨⟩ ⊢ bounded-program ⇒ tm-float_type
bounded-source = ⇒-conv
  (⇒-case wf[] refl (⇒-bounded_lit refl refl refl refl) sp[] sp[]
    bounded-motive-valid bounded-branches-valid bounded-coverage)
  (R.reduce-converts {t = tm-app bounded-motive (tm-bounded_lit 8)} {u = tm-float_type} β)
program-checked : ⟨⟩ ⊢ program ⇐ tm-float_type
program-checked = check program-source
bounded-checked : ⟨⟩ ⊢ bounded-program ⇐ tm-float_type
bounded-checked = check bounded-source
program-final : Final program
program-final = f-case f-nat_lit (f-lam (f-data ft[] ft[]) f-float_type)
  (fb∷ f-float_lit (fb∷ dependent-final fb[]))
bounded-final : Final bounded-program
bounded-final = f-case f-bounded_lit (f-lam (f-data ft[] ft[]) f-float_type)
  (fb∷ f-float_lit (fb∷ dependent-final fb[]))
program-admitted : Admitted ⟨⟩ program tm-float_type
program-admitted = record
  { signature-valid = valid; context-valid = wf[]
  ; term-scoped = sc-case sc-nat_lit (sc-lam nat-scoped sc-float_type)
      (sb∷ (sbranch sc-float_lit) (sb∷ (sbranch dependent-scoped) sb[]))
  ; goal-scoped = sc-float_type; goal-level = l0; goal-kind = ⇒-float_type
  ; checked = program-checked }
bounded-admitted : Admitted ⟨⟩ bounded-program tm-float_type
bounded-admitted = record
  { signature-valid = valid; context-valid = wf[]
  ; term-scoped = sc-case sc-bounded_lit (sc-lam bounded-scoped sc-float_type)
      (sb∷ (sbranch sc-float_lit) (sb∷ (sbranch dependent-scoped) sb[]))
  ; goal-scoped = sc-float_type; goal-level = l0; goal-kind = ⇒-float_type
  ; checked = bounded-checked }

step₁ : _⇝_ sig program dependent-program
step₁ = ι-nat-suc refl refl
bounded-step₁ : _⇝_ sig bounded-program dependent-program
bounded-step₁ = ι-bounded-suc refl refl
step₂ : _⇝_ sig dependent-program unfolded-program
step₂ = ξ-case (δ refl)
step₃ : _⇝_ sig unfolded-program tm-float_lit
step₃ = ι refl refl
program-path : _⇝*_ sig program tm-float_lit
program-path = ⇝*-step step₁ (⇝*-step step₂ (⇝*-step step₃ ⇝*-refl))
bounded-path : _⇝*_ sig bounded-program tm-float_lit
bounded-path = ⇝*-step bounded-step₁ (⇝*-step step₂ (⇝*-step step₃ ⇝*-refl))
