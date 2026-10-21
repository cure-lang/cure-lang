------------------------------------------------------------------------
-- Positive native Nat/Bounded fixture, with ordinary named fields.
-- Validity, conversion components and static shapes share ONE judgment.
------------------------------------------------------------------------
module Proof.DependentLiteralExamples where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Signature
open import Core.Coverage using (lookup-ctor-members; CaseCoverage; HasBranch)
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l≤-refl)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Reduction using (Signature; findBranch; substArgs; β; ζ)
import Core.DependentTyping as Native
import Proof.ReductionConversion as Reduction
import Proof.DependentDataConversion as Data
import Proof.DependentLiteralPreservation as Literal
import Proof.DependentTypingExamples as E
import Proof.DependentRootExamples as Roots

zero suc first next : Ctor
zero = record
  { ctor-name = "Z" ; ctor-args = [] ; ctor-params = [] ; ctor-indices = [] }
suc = record
  { ctor-name = "S" ; ctor-args = ("predecessor" , tm-data "LiteralNat" [] []) ∷ []
  ; ctor-params = [] ; ctor-indices = [] }
first = record
  { ctor-name = "First" ; ctor-args = ("initial-bound" , tm-data "LiteralNat" [] []) ∷ []
  ; ctor-params = [] ; ctor-indices = [] }
next = record
  { ctor-name = "Next"
  ; ctor-args = ("bound" , tm-data "LiteralNat" [] []) ∷
      ("previous" , tm-data "LiteralBounded" [] []) ∷ []
  ; ctor-params = [] ; ctor-indices = [] }

nat bounded : Family
nat = record
  { fam-name = "LiteralNat" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = zero ∷ suc ∷ [] ; positive = true ; universe-ok = true }
bounded = record
  { fam-name = "LiteralBounded" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = first ∷ next ∷ [] ; positive = true ; universe-ok = true }

identities : Name → Maybe Name
identities key with key ≟ "nat"
... | yes same = just "LiteralNat"
... | no different with key ≟ "bounded"
... | yes same = just "LiteralBounded"
... | no different = nothing

env : IndEnv
env = record { families = nat ∷ bounded ∷ [] ; builtins = identities }
sig : Signature
sig = record { body = λ _ → nothing ; type-of = λ _ → nothing }
module R = Reduction.Model sig (λ ())
conv : Conversion
conv = R.conversion
module D = Data.Model sig (λ ())
module T = Native.Typing env sig conv
open T

nat-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-data "LiteralNat" [] [] ⇒ Core.Syntax.tm-type l0
nat-kind = ⇒-data refl sp[] sp[]
bounded-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-data "LiteralBounded" [] [] ⇒ Core.Syntax.tm-type l0
bounded-kind = ⇒-data refl sp[] sp[]
nat-scoped : ∀ {n} → Scoped n (tm-data "LiteralNat" [] [])
nat-scoped = sc-data st[] st[]
bounded-scoped : ∀ {n} → Scoped n (tm-data "LiteralBounded" [] [])
bounded-scoped = sc-data st[] st[]

nat-declaration : FamilyDeclaration nat
nat-declaration = record
  { parameter-context = ⟨⟩ ; index-context = ⟨⟩ ; parameters = dt[] ; indices = dt[] }
bounded-declaration : FamilyDeclaration bounded
bounded-declaration = record
  { parameter-context = ⟨⟩ ; index-context = ⟨⟩ ; parameters = dt[] ; indices = dt[] }
zero-declaration : ConstructorDeclaration nat zero
zero-declaration = record
  { parameter-context = ⟨⟩ ; field-context = ⟨⟩
  ; parameters = dt[] ; fields = dt[] ; field-levels = tt
  ; result-scoping = st[] , st[] ; uniform-parameters = refl
  ; result-parameters = sp[] ; result-indices = sp[] }
suc-declaration : ConstructorDeclaration nat suc
suc-declaration = record
  { parameter-context = ⟨⟩ ; field-context = extend ⟨⟩ (tm-data "LiteralNat" [] [])
  ; parameters = dt[] ; fields = dt∷ nat-scoped nat-kind dt[]
  ; field-levels = l≤-refl , tt
  ; result-scoping = st[] , st[] ; uniform-parameters = refl
  ; result-parameters = sp[] ; result-indices = sp[] }
first-declaration : ConstructorDeclaration bounded first
first-declaration = record
  { parameter-context = ⟨⟩ ; field-context = extend ⟨⟩ (tm-data "LiteralNat" [] [])
  ; parameters = dt[] ; fields = dt∷ nat-scoped nat-kind dt[]
  ; field-levels = l≤-refl , tt
  ; result-scoping = st[] , st[] ; uniform-parameters = refl
  ; result-parameters = sp[] ; result-indices = sp[] }
next-declaration : ConstructorDeclaration bounded next
next-declaration = record
  { parameter-context = ⟨⟩
  ; field-context = extend (extend ⟨⟩ (tm-data "LiteralNat" [] [])) (tm-data "LiteralBounded" [] [])
  ; parameters = dt[] ; fields = dt∷ nat-scoped nat-kind (dt∷ bounded-scoped bounded-kind dt[])
  ; field-levels = l≤-refl , l≤-refl , tt
  ; result-scoping = st[] , st[] ; uniform-parameters = refl
  ; result-parameters = sp[] ; result-indices = sp[] }

family-valid : ∀ {name f} → findFamily name (IndEnv.families env) ≡ just f → FamilyDeclaration f
family-valid {name} found with name ≟ "LiteralNat"
... | yes refl with just-inj found
... | refl = nat-declaration
family-valid {name} found | no different with name ≟ "LiteralBounded"
... | yes refl with just-inj found
... | refl = bounded-declaration
family-valid {name} () | no different | no other

ctor-valid : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → ConstructorDeclaration f ct
ctor-valid {name} found with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , equal = zero-declaration
... | here refl , there (here refl) , equal = suc-declaration
... | here refl , there (there ()) , equal
... | there (here refl) , here refl , equal = first-declaration
... | there (here refl) , there (here refl) , equal = next-declaration
... | there (here refl) , there (there ()) , equal
... | there (there ()) , member , equal

owner-visible : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct)
  → findFamily (fam-name f) (IndEnv.families env) ≡ just f
owner-visible {name} found with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , member , equal = refl
... | there (here refl) , member , equal = refl
... | there (there ()) , member , equal

valid : SignatureValid
valid = record
  { family-declared = λ {name} → family-valid {name}
  ; constructor-declared = λ {name} → ctor-valid {name}
  ; owner-visible = λ {name} → owner-visible {name}
  ; global-type = λ () ; global-body = λ () }

nat-shape : Literal.NatShape env "LiteralNat" nat
nat-shape = record
  { predecessor = "predecessor"
  ; zero-shape = record { ctor = zero ; found = refl ; fields = refl ; results = refl }
  ; suc-shape = record { ctor = suc ; found = refl ; fields = refl ; results = refl } }
bounded-shape : Literal.BoundedShape env "LiteralBounded" bounded
bounded-shape = record
  { nat-name = "LiteralNat" ; nat-family = nat
  ; nat-builtin = refl ; nat-found = refl ; nat-parameters = refl ; nat-indices = refl
  ; bound = "bound" ; first-bound = "initial-bound" ; predecessor = "previous"
  ; zero-shape = record { ctor = first ; found = refl ; fields = refl ; results = refl }
  ; suc-shape = record { ctor = next ; found = refl ; fields = refl ; results = refl } }

nat-shape-at : ∀ {name family} → identities "nat" ≡ just name
  → findFamily name (IndEnv.families env) ≡ just family
  → fam-params family ≡ [] → fam-indices family ≡ []
  → Literal.NatShape env name family
nat-shape-at identity found pars inds with just-inj identity
... | refl with just-inj found
... | refl = nat-shape
bounded-shape-at : ∀ {name family} → identities "bounded" ≡ just name
  → findFamily name (IndEnv.families env) ≡ just family
  → fam-params family ≡ [] → fam-indices family ≡ []
  → Literal.BoundedShape env name family
bounded-shape-at identity found pars inds with just-inj identity
... | refl with just-inj found
... | refl = bounded-shape
shapes : Literal.BuiltinShapes env
shapes = record { nat-shape = nat-shape-at ; bounded-shape = bounded-shape-at }
module L = Literal.Laws env sig conv valid D.data-components R.reduce-converts shapes

-- Existing non-builtin native environments remain admissible vacuously.
existing-shapes : Literal.BuiltinShapes E.env
existing-shapes = Literal.no-builtins E.env (λ key → refl)
global-shapes : Literal.BuiltinShapes Roots.Globals.env
global-shapes = Literal.no-builtins Roots.Globals.env (λ key → refl)

check : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ⇒ A → Γ ⊢ t ⇐ A
check {A = A} typed = ⇐-infer typed (Conversion.≈-refl conv {t = A})

nat-motive bounded-motive : Term
nat-motive = tm-lam unrestricted (tm-data "LiteralNat" [] []) tm-float_type
bounded-motive = tm-lam unrestricted (tm-data "LiteralBounded" [] []) tm-float_type
nat-motive-valid : Motive ⟨⟩ nat [] nat-motive l0
nat-motive-valid = motive (sc-lam nat-scoped sc-float_type)
  (⇒-pi nat-kind (⇒-type refl)) (⇒-lam nat-kind (check ⇒-float_type))
bounded-motive-valid : Motive ⟨⟩ bounded [] bounded-motive l0
bounded-motive-valid = motive (sc-lam bounded-scoped sc-float_type)
  (⇒-pi bounded-kind (⇒-type refl)) (⇒-lam bounded-kind (check ⇒-float_type))

float-body : ∀ {n} {Γ : Ctx n} {domain arg}
  → Γ ⊢ tm-float_lit ⇐ tm-app (tm-lam unrestricted domain tm-float_type) arg
float-body {domain = domain} {arg} = ⇐-infer ⇒-float_lit
  (Conversion.≈-sym conv
    {t = tm-app (tm-lam unrestricted domain tm-float_type) arg} {u = tm-float_type}
    (R.reduce-converts {t = tm-app (tm-lam unrestricted domain tm-float_type) arg}
      {u = tm-float_type} β))

nat-branches bounded-branches : Data.List.List Branch
nat-branches = ("Z" , 0 , tm-float_lit) ∷ ("S" , 1 , tm-float_lit) ∷ []
bounded-branches = ("First" , 1 , tm-float_lit) ∷ ("Next" , 2 , tm-float_lit) ∷ []
nat-branches-valid : Branches ⟨⟩ nat [] nat-motive nat-branches
nat-branches-valid = br∷ refl refl Native.op[] wf[] float-body
  (br∷ refl refl (Native.op∷ Native.op[]) (wf∷ wf[] nat-scoped nat-kind) float-body br[])
bounded-branches-valid : Branches ⟨⟩ bounded [] bounded-motive bounded-branches
bounded-branches-valid = br∷ refl refl (Native.op∷ Native.op[])
  (wf∷ wf[] nat-scoped nat-kind) float-body
  (br∷ refl refl (Native.op∷ (Native.op∷ Native.op[]))
    (wf∷ (wf∷ wf[] nat-scoped nat-kind) bounded-scoped bounded-kind) float-body br[])

nat-covered : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → fam-name f ≡ "LiteralNat"
  → HasBranch name (Data.List.length (ctor-args ct)) nat-branches
nat-covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , refl = tm-float_lit , refl
... | here refl , there (here refl) , refl = tm-float_lit , refl
... | here refl , there (there ()) , equal
nat-covered found () | there (here refl) , member , equal
nat-covered found owner | there (there ()) , member , equal
bounded-covered : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → fam-name f ≡ "LiteralBounded"
  → HasBranch name (Data.List.length (ctor-args ct)) bounded-branches
bounded-covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
bounded-covered found () | here refl , member , equal
... | there (here refl) , here refl , refl = tm-float_lit , refl
... | there (here refl) , there (here refl) , refl = tm-float_lit , refl
... | there (here refl) , there (there ()) , equal
... | there (there ()) , member , equal

nat-coverage : CaseCoverage env "LiteralNat" nat-branches
nat-coverage = record
  { ctor-covered = λ {name} → nat-covered {name}
  ; nat-zero-covered = λ identity → tm-float_lit , refl
  ; nat-suc-covered = λ identity → tm-float_lit , refl
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }
bounded-coverage : CaseCoverage env "LiteralBounded" bounded-branches
bounded-coverage = record
  { ctor-covered = λ {name} → bounded-covered {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ identity → tm-float_lit , refl
  ; bounded-suc-covered = λ identity → tm-float_lit , refl }

nat-frame : L.C.CaseFrame ⟨⟩ "LiteralNat" [] [] nat nat-motive l0 nat-branches
nat-frame = record
  { wf = wf[] ; found = refl ; parameters = sp[] ; indices = sp[]
  ; motive-typed = nat-motive-valid ; branches = nat-branches-valid ; covered = nat-coverage }
bounded-frame : L.C.CaseFrame ⟨⟩ "LiteralBounded" [] [] bounded bounded-motive l0 bounded-branches
bounded-frame = record
  { wf = wf[] ; found = refl ; parameters = sp[] ; indices = sp[]
  ; motive-typed = bounded-motive-valid ; branches = bounded-branches-valid ; covered = bounded-coverage }

nat-zero-preserved : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps nat-motive (tm-nat_lit 0 ∷ [])
nat-zero-preserved = L.nat-zero nat-frame (⇒-nat_lit refl refl refl refl) refl refl
nat-suc-preserved : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps nat-motive (tm-nat_lit 8 ∷ [])
nat-suc-preserved = L.nat-suc nat-frame (⇒-nat_lit refl refl refl refl) refl refl
bounded-zero-preserved : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps bounded-motive (tm-bounded_lit 0 ∷ [])
bounded-zero-preserved = L.bounded-zero bounded-frame (⇒-bounded_lit refl refl refl refl) refl refl
bounded-suc-preserved : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps bounded-motive (tm-bounded_lit 8 ∷ [])
bounded-suc-preserved = L.bounded-suc bounded-frame (⇒-bounded_lit refl refl refl refl) refl refl

nat-goal bounded-goal wrapped-nat wrapped-bounded : Term
nat-goal = tm-data "LiteralNat" [] []
bounded-goal = tm-data "LiteralBounded" [] []
wrapped-nat = tm-let unrestricted (tm-type l0) nat-goal (tm-var 0)
wrapped-bounded = tm-let unrestricted (tm-type l0) bounded-goal (tm-var 0)
nat-unwrap : Conversion._≈_ conv wrapped-nat nat-goal
nat-unwrap = R.reduce-converts {t = wrapped-nat} {u = nat-goal} ζ
bounded-unwrap : Conversion._≈_ conv wrapped-bounded bounded-goal
bounded-unwrap = R.reduce-converts {t = wrapped-bounded} {u = bounded-goal} ζ

nat-chain : ∀ k → ⟨⟩ ⊢ tm-nat_lit k ⇒ nat-goal
nat-chain k = ⇒-conv {T = wrapped-nat} {T′ = nat-goal}
  (⇒-conv {T = nat-goal} {T′ = wrapped-nat} (⇒-nat_lit refl refl refl refl)
    (Conversion.≈-sym conv {t = wrapped-nat} {u = nat-goal} nat-unwrap)) nat-unwrap
bounded-chain : ∀ k → ⟨⟩ ⊢ tm-bounded_lit k ⇒ bounded-goal
bounded-chain k = ⇒-conv {T = wrapped-bounded} {T′ = bounded-goal}
  (⇒-conv {T = bounded-goal} {T′ = wrapped-bounded} (⇒-bounded_lit refl refl refl refl)
    (Conversion.≈-sym conv {t = wrapped-bounded} {u = bounded-goal} bounded-unwrap)) bounded-unwrap

nat-check-chain : ∀ k → ⟨⟩ ⊢ tm-nat_lit k ⇐ nat-goal
nat-check-chain k = ⇐-conv {T = wrapped-nat} {T′ = nat-goal}
  (⇐-infer (nat-chain k)
    (Conversion.≈-sym conv {t = wrapped-nat} {u = nat-goal} nat-unwrap)) nat-unwrap
bounded-check-chain : ∀ k → ⟨⟩ ⊢ tm-bounded_lit k ⇐ bounded-goal
bounded-check-chain k = ⇐-conv {T = wrapped-bounded} {T′ = bounded-goal}
  (⇐-infer (bounded-chain k)
    (Conversion.≈-sym conv {t = wrapped-bounded} {u = bounded-goal} bounded-unwrap)) bounded-unwrap
nat-check-inversion : ∀ k → L.LiteralView Literal.nat nat-goal
nat-check-inversion k = L.check-literal Literal.nat (nat-check-chain k)
bounded-check-inversion : ∀ k → L.LiteralView Literal.bounded bounded-goal
bounded-check-inversion k = L.check-literal Literal.bounded (bounded-check-chain k)

converted-nat-zero : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps nat-motive (tm-nat_lit 0 ∷ [])
converted-nat-zero = L.nat-zero nat-frame (nat-chain 0) refl refl
converted-nat-suc : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps nat-motive (tm-nat_lit 8 ∷ [])
converted-nat-suc = L.nat-suc nat-frame (nat-chain 8) refl refl
converted-bounded-zero : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps bounded-motive (tm-bounded_lit 0 ∷ [])
converted-bounded-zero = L.bounded-zero bounded-frame (bounded-chain 0) refl refl
converted-bounded-suc : ⟨⟩ ⊢ tm-float_lit ⇐ Native.apps bounded-motive (tm-bounded_lit 8 ∷ [])
converted-bounded-suc = L.bounded-suc bounded-frame (bounded-chain 8) refl refl
