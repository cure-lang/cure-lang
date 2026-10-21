------------------------------------------------------------------------
-- One canonical snapshot, supported payloads and genuinely dependent
-- native case. This does NOT derive typing from an executable checker.
------------------------------------------------------------------------
module Proof.AdmissionBoundaryExamples where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Nat using (z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; length)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.String.Properties using (_≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l≤-refl; l0≤l1)
open import Core.Signature
open import Core.Reduction
open import Core.Coverage
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
import Core.DependentTyping as Native
import Core.CanonicalSnapshot as S
import Core.AdmissionBoundary as Boundary
import Proof.ReductionConversion as Reduction
import Proof.DependentProgress as Progress

ctor : Ctor
ctor = record
  { ctor-name = "Boundary#Pack"
  ; ctor-args = ("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ []
  ; ctor-params = [] ; ctor-indices = tm-var 1 ∷ [] }
family : Family
family = record
  { fam-name = "Boundary#Packed" ; fam-params = []
  ; fam-indices = ("A" , tm-type l0) ∷ [] ; fam-level = l1
  ; fam-ctors = ctor ∷ [] ; positive = true ; universe-ok = true }
answer : S.Global
answer = S.global tm-atom_type (just (tm-atom_lit "answer"))
snapshot : S.Snapshot
snapshot = record
  { family-entries = family ∷ []
  ; globals = ("Boundary#answer" , answer) ∷ []
  ; family-keys = S.unique∷ S.fresh[] S.unique[]
  ; constructor-keys = S.unique∷ S.fresh[] S.unique[]
  ; global-keys = S.unique∷ S.fresh[] S.unique[] }
open S.Snapshot snapshot using (ind; sig)
module B = Boundary.Fragment snapshot
open B

-- These equations consume the derived general lookup correspondence.
family-found : findFamily "Boundary#Packed" (IndEnv.families ind) ≡ just family
family-found = sym (S.family-lookup-agrees "Boundary#Packed" (family ∷ []))
ctor-found : findCtor "Boundary#Pack" (IndEnv.families ind) ≡ just (family , ctor)
ctor-found = sym (S.constructor-lookup-agrees "Boundary#Pack" (family ∷ []))
global-found : Signature.body sig "Boundary#answer" ≡ just (tm-atom_lit "answer")
global-found = S.global-body-found
  {globals = ("Boundary#answer" , answer) ∷ []} {key = "Boundary#answer"} {entry = answer} refl

body-closed : ∀ {name b} → Signature.body sig name ≡ just b → Scoped 0 b
body-closed {name} found with name ≟ "Boundary#answer"
... | yes same with just-inj found
... | refl = sc-atom_lit
body-closed {name} () | no different
module R = Reduction.Model sig (λ {name} → body-closed {name})
conv : Conversion
conv = R.conversion
module N = Native.Typing ind sig conv
open N
check : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Γ ⊢ t ⇐ T
check {T = T} typed = ⇐-infer typed (Conversion.≈-refl conv {t = T})

Π : Ctx 1
Π = extend ⟨⟩ (tm-type l0)
Φ : Ctx 2
Φ = extend Π (tm-var 0)
family-declaration : FamilyDeclaration family
family-declaration = record
  { parameter-context = ⟨⟩ ; index-context = Π
  ; parameters = dt[] ; indices = dt∷ sc-type (⇒-type refl) dt[] }
ctor-declaration : ConstructorDeclaration family ctor
ctor-declaration = record
  { parameter-context = ⟨⟩ ; field-context = Φ ; parameters = dt[]
  ; fields = dt∷ sc-type (⇒-type refl)
      (dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[])
  ; field-levels = l≤-refl , l0≤l1 , tt
  ; result-scoping = st[] , st∷ (sc-var (s≤s (s≤s z≤n))) st[]
  ; uniform-parameters = refl ; result-parameters = sp[]
  ; result-indices = sp∷ (check (⇒-var (Fin.suc Fin.zero))) sp[] }
family-declared : ∀ {name f} → findFamily name (IndEnv.families ind) ≡ just f
  → FamilyDeclaration f
family-declared {name} found with name ≟ "Boundary#Packed"
... | yes refl with just-inj found
... | refl = family-declaration
family-declared {name} () | no different
ctor-declared : ∀ {name f ct} → findCtor name (IndEnv.families ind) ≡ just (f , ct)
  → ConstructorDeclaration f ct
ctor-declared {name} found with lookup-ctor-members {c = name} {fs = family ∷ []} found
... | here refl , here refl , equal = ctor-declaration
... | here refl , there () , equal
... | there () , member , equal
owner-visible : ∀ {name f ct} → findCtor name (IndEnv.families ind) ≡ just (f , ct)
  → findFamily (fam-name f) (IndEnv.families ind) ≡ just f
owner-visible {name} = S.Snapshot.owner-visible snapshot {name = name}
global-kind : ∀ {name T} → Signature.type-of sig name ≡ just T
  → Scoped 0 T × (Data.Product.∃ λ l → ⟨⟩ ⊢ T ⇒ tm-type l)
global-kind {name} found with name ≟ "Boundary#answer"
... | yes same with just-inj found
... | refl = sc-atom_type , l0 , ⇒-atom_type
global-kind {name} () | no different
global-typed : ∀ {name b} → Signature.body sig name ≡ just b
  → Data.Product.∃ λ T → Signature.type-of sig name ≡ just T
    × Scoped 0 b × (⟨⟩ ⊢ b ⇒ T)
global-typed {name} found with name ≟ "Boundary#answer"
... | yes same with just-inj found
... | refl = tm-atom_type , refl , sc-atom_lit , ⇒-atom_lit
global-typed {name} () | no different
valid : SignatureValid
valid = record
  { family-declared = λ {name} → family-declared {name}
  ; constructor-declared = λ {name} → ctor-declared {name}
  ; owner-visible = λ {name} → owner-visible {name}
  ; global-type = λ {name} → global-kind {name}
  ; global-body = λ {name} → global-typed {name} }

value goal motive-term program : Term
value = tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
goal = tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])
motive-term = tm-lam unrestricted (tm-type l0)
  (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1))
branches : List Branch
branches = ("Boundary#Pack" , 2 , tm-var 0) ∷ []
program = tm-case value motive-term branches
value-supported : Supported 0 value
value-supported = s-ctor refl (s∷ s-atom_type (s∷ s-atom_lit s[]))
goal-supported : Supported 0 goal
goal-supported = s-data refl s[] (s∷ s-atom_type s[])
motive-supported : Supported 0 motive-term
motive-supported = s-lam s-type
  (s-lam (s-data refl s[] (s∷ (s-var (s≤s z≤n)) s[])) (s-var (s≤s (s≤s z≤n))))
program-supported : Supported 0 program
program-supported = s-case value-supported motive-supported
  (b∷ refl refl (s-var (s≤s z≤n)) b[])
payloads-supported : PayloadsSupported
payloads-supported = record
  { declarations = record
      { parameters = t[] ; indices = t∷ s-type t[]
      ; constructors = record
          { fields = t∷ s-type (t∷ (s-var (s≤s z≤n)) t[])
          ; result-parameters = s[]
          ; result-indices = s∷ (s-var (s≤s (s≤s z≤n))) s[] } All.∷ All.[] } All.∷ All.[]
  ; definitions = record { type = s-atom_type ; body = s-atom_lit } All.∷ All.[] }

value-typed : ⟨⟩ ⊢ value ⇒ goal
value-typed = ⇒-ctor ctor-found sp[]
  (sp∷ (check ⇒-atom_type) (sp∷ (check ⇒-atom_lit) sp[]))
motive-kind : ⟨⟩ ⊢ Native.motiveType family [] l0 ⇒ tm-type l1
motive-kind = ⇒-pi (⇒-type refl)
  (⇒-pi (⇒-data family-found sp[] (sp∷ (check (⇒-var Fin.zero)) sp[])) (⇒-type refl))
motive-typed : ⟨⟩ ⊢ motive-term ⇒ Native.motiveType family [] l0
motive-typed = ⇒-lam (⇒-type refl)
  (⇐-lam (⇒-data family-found sp[] (sp∷ (check (⇒-var Fin.zero)) sp[]))
    (check (⇒-var (Fin.suc Fin.zero))))
branch-context : WellFormed Φ
branch-context = wf∷ (wf∷ wf[] sc-type (⇒-type refl))
  (sc-var (s≤s z≤n)) (⇒-var Fin.zero)
branch-middle : Term
branch-middle = tm-app
  (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 1 ∷ [])) (tm-var 2))
  (tm-ctor "Boundary#Pack" (tm-var 1 ∷ tm-var 0 ∷ []))
branch-converts : Conversion._≈_ conv
  (Native.branchGoal "Boundary#Pack" [] ctor motive-term) (tm-var 1)
branch-converts = Conversion.≈-trans conv
  {t = Native.branchGoal "Boundary#Pack" [] ctor motive-term}
  {u = branch-middle} {v = tm-var 1}
  (R.reduce-converts
    {t = Native.branchGoal "Boundary#Pack" [] ctor motive-term}
    {u = branch-middle} (ξ-app₁ β))
  (R.reduce-converts {t = branch-middle} {u = tm-var 1} β)
branch-typed : N.Branches ⟨⟩ family [] motive-term branches
branch-typed = br∷ ctor-found refl (Native.op∷ (Native.op∷ Native.op[])) branch-context
  (⇐-infer (⇒-var Fin.zero) (Conversion.≈-sym conv
    {t = Native.branchGoal "Boundary#Pack" [] ctor motive-term}
    {u = tm-var 1} branch-converts)) br[]
covered : ∀ {name f ct} → findCtor name (IndEnv.families ind) ≡ just (f , ct)
  → fam-name f ≡ "Boundary#Packed" → HasBranch name (length (ctor-args ct)) branches
covered {name} found owner with lookup-ctor-members {c = name} {fs = family ∷ []} found
... | here refl , here refl , refl = tm-var 0 , refl
... | here refl , there () , equal
... | there () , member , equal
coverage : CaseCoverage ind "Boundary#Packed" branches
coverage = record
  { ctor-covered = λ {name} → covered {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }
program-typed : ⟨⟩ ⊢ program ⇐ tm-atom_type
program-typed = ⇐-infer
  (⇒-case wf[] family-found value-typed sp[] (sp∷ (check ⇒-atom_type) sp[])
    (motive (scoped motive-supported) motive-kind motive-typed) branch-typed coverage)
  (Conversion.≈-trans conv
    {t = Native.apps motive-term (tm-atom_type ∷ value ∷ [])}
    {u = tm-app (tm-lam unrestricted goal tm-atom_type) value}
    {v = tm-atom_type}
    (R.reduce-converts
      {t = Native.apps motive-term (tm-atom_type ∷ value ∷ [])}
      {u = tm-app (tm-lam unrestricted goal tm-atom_type) value} (ξ-app₁ β))
    (R.reduce-converts
      {t = tm-app (tm-lam unrestricted goal tm-atom_type) value} {u = tm-atom_type} β))
module A = B.Admission conv
eligible : A.Eligible ⟨⟩ program tm-atom_type
eligible = record
  { payloads = payloads-supported ; caller = λ ()
  ; source = program-supported ; goal = s-atom_type
  ; native = record
      { signature-valid = valid ; context-valid = wf[]
      ; term-scoped = scoped program-supported ; goal-scoped = sc-atom_type
      ; goal-level = l0 ; goal-kind = ⇒-atom_type ; checked = program-typed } }

module P = Progress.Progress ind sig conv
ready : Value program Data.Sum.⊎ (Data.Product.∃ λ u → _⇝_ sig program u)
ready = P.progress⇐ (A.Eligible.checked eligible) (A.Eligible.source-final eligible)

contracts-at-original-goal : _⇝_ sig program (tm-atom_lit "payload")
contracts-at-original-goal = ι refl refl

-- Successful syntax is not typing: the universe ceiling is represented,
-- but native sort inference still rejects Type2 as a well-kinded domain.
ceiling-supported : Supported 0 (tm-type Core.Universe.l2)
ceiling-supported = s-type

missing-global : Supported 0 (tm-global "missing") → ⊥
missing-global (s-global ())
foreign-family : Supported 0 (tm-data "Foreign#Packed" [] []) → ⊥
foreign-family (s-data () ps is)
bare-constructor : Supported 0 (tm-ctor "Pack" []) → ⊥
bare-constructor (s-ctor () args)
float-excluded : ∀ {n} → Supported n tm-float_lit → ⊥
float-excluded ()
int-excluded : ∀ {n k} → Supported n (tm-int_lit k) → ⊥
int-excluded ()
nat-excluded : ∀ {n k} → Supported n (tm-nat_lit k) → ⊥
nat-excluded ()
bounded-excluded : ∀ {n k} → Supported n (tm-bounded_lit k) → ⊥
bounded-excluded ()
effect-excluded : ∀ {n e k} → Supported n (tm-effect_bind e k) → ⊥
effect-excluded ()
hole-excluded : ∀ {n name} → Supported n (tm-hole name) → ⊥
hole-excluded ()
absurd-excluded : ∀ {n} → Supported n tm-absurd → ⊥
absurd-excluded ()
escaped-source : Supported 0 (tm-var 0) → ⊥
escaped-source (s-var ())
escaped-branch : B.Branches 0 (("Boundary#Pack" , 2 , tm-var 2) ∷ []) → ⊥
escaped-branch (b∷ found arity (s-var (s≤s (s≤s ()))) rest)
bad-arity : B.Branches 0 (("Boundary#Pack" , 1 , tm-var 0) ∷ []) → ⊥
bad-arity (b∷ found arity body rest) with just-inj found
... | refl with arity
... | ()
