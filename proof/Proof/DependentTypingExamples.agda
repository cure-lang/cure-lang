------------------------------------------------------------------------
-- Native interface witnesses, NOT a native preservation/progress proof.
-- One environment checks declarations, nested family fields, motives and
-- whole cases. Conversion is the inhabited full reduction model, with no
-- base typing/preservation/closed-entry premise.
------------------------------------------------------------------------
module Proof.DependentTypingExamples where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; z≤n; s≤s)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l≤-refl; l0≤l1)
open import Core.Signature
open import Core.Reduction
open import Core.Coverage
open import Core.ClosedFragment using (family-lookup-member)
open import Core.Typing using (Ctx; ⟨⟩; extend; lookup; Conversion)
open import Core.DependentTyping
import Core.LocalFrame as F
import Proof.ReductionConversion as Reduction
open import Proof.Substitution using (subst-extSub-wk; topSub-rename)

sig : Signature
sig = record { body = λ _ → nothing ; type-of = λ _ → nothing }

module R = Reduction.Model sig (λ ())
conv : Conversion
conv = R.conversion
open Conversion

parameters indices : Telescope
parameters = ("A" , tm-type l0) ∷ []
indices = ("x" , tm-var 0) ∷ ("B" , tm-type l0) ∷ ("y" , tm-var 0) ∷ []
computed-index : Term
computed-index = tm-app (tm-lam unrestricted (tm-var 3) (tm-var 0)) (tm-var 2)
mk computed : Ctor
mk = record
  { ctor-name = "NativeMk" ; ctor-args = indices
  ; ctor-params = tm-var 3 ∷ []
  ; ctor-indices = tm-var 2 ∷ tm-var 1 ∷ tm-var 0 ∷ [] }
computed = record mk
  { ctor-name = "NativeComputed"
  ; ctor-indices = computed-index ∷ tm-var 1 ∷ tm-var 0 ∷ [] }
family : Family
family = record
  { fam-name = "NativeD" ; fam-params = parameters ; fam-indices = indices
  ; fam-level = l1 ; fam-ctors = mk ∷ computed ∷ []
  ; positive = true ; universe-ok = true }

fields : List Term
fields = tm-atom_lit "payload" ∷ tm-float_type ∷ tm-float_lit ∷ []
goal value : Term
goal = tm-data "NativeD" (tm-atom_type ∷ []) fields
value = tm-ctor "NativeMk" fields

-- Both the wrapper INDEX declaration and its field type use the new D.
wrap : Ctor
wrap = record
  { ctor-name = "NativeWrap" ; ctor-args = ("d" , goal) ∷ []
  ; ctor-params = [] ; ctor-indices = tm-var 0 ∷ [] }
wrapper : Family
wrapper = record
  { fam-name = "NativeWrapper" ; fam-params = []
  ; fam-indices = ("d" , goal) ∷ []
  ; fam-level = l1 ; fam-ctors = wrap ∷ []
  ; positive = true ; universe-ok = true }
env : IndEnv
env = record { families = family ∷ wrapper ∷ [] ; builtins = λ _ → nothing }
module T = Core.DependentTyping.Typing env sig conv
open T

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
local-computed : Φ ⊢
  tm-app (tm-lam unrestricted (tm-var 3) (tm-var 0)) (tm-var 2) ⇒ tm-var 3
local-computed = ⇒-app
  (⇒-lam {c = tm-var 4} (⇒-var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
    (check (⇒-var Fin.zero))) (⇒-var (Fin.suc (Fin.suc Fin.zero)))

family-declaration : FamilyDeclaration family
family-declaration = record
  { parameter-context = Π ; index-context = Φ
  ; parameters = parameters-declared ; indices = indices-declared }
mk-declaration : ConstructorDeclaration family mk
mk-declaration = record
  { parameter-context = Π ; field-context = Φ
  ; parameters = parameters-declared ; fields = indices-declared
  ; field-levels = l0≤l1 , l≤-refl , l0≤l1 , tt
  ; result-scoping = st∷ (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) st[] ,
      st∷ (sc-var (s≤s (s≤s (s≤s z≤n))))
        (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[]))
  ; uniform-parameters = refl
  ; result-parameters = local-parameters ; result-indices = local-indices }
computed-declaration : ConstructorDeclaration family computed
computed-declaration = record
  { parameter-context = Π ; field-context = Φ
  ; parameters = parameters-declared ; fields = indices-declared
  ; field-levels = l0≤l1 , l≤-refl , l0≤l1 , tt
  ; result-scoping = st∷ (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) st[] ,
      st∷ (sc-app (sc-lam (sc-var (s≤s (s≤s (s≤s (s≤s z≤n))))) (sc-var (s≤s z≤n)))
        (sc-var (s≤s (s≤s (s≤s z≤n)))))
        (st∷ (sc-var (s≤s (s≤s z≤n))) (st∷ (sc-var (s≤s z≤n)) st[]))
  ; uniform-parameters = refl
  ; result-parameters = local-parameters
  ; result-indices = sp∷ (check local-computed)
      (sp∷ (check (⇒-var (Fin.suc Fin.zero))) (sp∷ (check (⇒-var Fin.zero)) sp[])) }

actual-parameters : ∀ {n} {Γ : Ctx n} → Spine Γ [] (tm-atom_type ∷ []) parameters
actual-parameters = sp∷ (check ⇒-atom_type) sp[]
actual-fields : ∀ {n} {Γ : Ctx n} → Spine Γ (tm-atom_type ∷ []) fields indices
actual-fields = sp∷ (check ⇒-atom_lit)
  (sp∷ (check ⇒-float_type) (sp∷ (check ⇒-float_lit) sp[]))
goal-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ goal ⇒ tm-type l1
goal-kind = ⇒-data refl actual-parameters actual-fields
value-typed : ∀ {n} {Γ : Ctx n} → Γ ⊢ value ⇒ goal
value-typed = ⇒-ctor refl actual-parameters actual-fields
computed-typed : ⟨⟩ ⊢ tm-ctor "NativeComputed" fields ⇒
  tm-data "NativeD" (tm-atom_type ∷ []) (F.instantiateResults (tm-atom_type ∷ []) fields (ctor-indices computed))
computed-typed = ⇒-ctor refl actual-parameters actual-fields

goal-scoped : ∀ {n} → Scoped n goal
goal-scoped = sc-data (st∷ sc-atom_type st[])
  (st∷ sc-atom_lit (st∷ sc-float_type (st∷ sc-float_lit st[])))
wrapper-declaration : FamilyDeclaration wrapper
wrapper-declaration = record
  { parameter-context = ⟨⟩ ; index-context = extend ⟨⟩ goal
  ; parameters = dt[] ; indices = dt∷ goal-scoped goal-kind dt[] }
wrap-declaration : ConstructorDeclaration wrapper wrap
wrap-declaration = record
  { parameter-context = ⟨⟩ ; field-context = extend ⟨⟩ goal
  ; parameters = dt[] ; fields = dt∷ goal-scoped goal-kind dt[]
  ; field-levels = l≤-refl , tt
  ; result-scoping = st[] , st∷ (sc-var (s≤s z≤n)) st[]
  ; uniform-parameters = refl ; result-parameters = sp[]
  ; result-indices = sp∷ (check (⇒-var Fin.zero)) sp[] }

family-declared : ∀ {name f} → findFamily name (IndEnv.families env) ≡ just f → FamilyDeclaration f
family-declared {name} found with family-lookup-member {name = name} {fs = IndEnv.families env} found
... | here refl = family-declaration
... | there (here refl) = wrapper-declaration
... | there (there ())
constructor-declared : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct) → ConstructorDeclaration f ct
constructor-declared {name} found with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , equal = mk-declaration
... | here refl , there (here refl) , equal = computed-declaration
... | here refl , there (there ()) , equal
... | there (here refl) , here refl , equal = wrap-declaration
... | there (here refl) , there () , equal
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
  { family-declared = λ {name} → family-declared {name}
  ; constructor-declared = λ {name} → constructor-declared {name}
  ; owner-visible = λ {name} → owner-visible {name}
  ; global-type = λ () ; global-body = λ () }

wrapped-typed : ⟨⟩ ⊢ tm-ctor "NativeWrap" (value ∷ []) ⇒
  tm-data "NativeWrapper" [] (value ∷ [])
wrapped-typed = ⇒-ctor refl sp[] (sp∷ (check value-typed) sp[])
wrapped-kind : ⟨⟩ ⊢ tm-data "NativeWrapper" [] (value ∷ []) ⇒ tm-type l1
wrapped-kind = ⇒-data refl sp[] (sp∷ (check value-typed) sp[])

-- Open the three fields in any caller; parameters do not become binders.
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
    (cong (rename wk) (topSub-rename y B))))
  (topSub-rename s B)

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
covered-ctor found owner | there (there ()) , member , equal
coverage : CaseCoverage env "NativeD" branches
coverage = record
  { ctor-covered = λ {name} → covered-ctor {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }

program : Term
program = tm-case value motive-term branches
program-typed : ⟨⟩ ⊢ program ⇒ tm-float_type
program-typed = ⇒-conv
  (⇒-case wf[] refl value-typed actual-parameters actual-fields motive-valid (branches-typed wf[]) coverage)
  (motive-reduces (tm-atom_lit "payload") tm-float_type tm-float_lit value)

value-admitted : Admitted ⟨⟩ value goal
value-admitted = record
  { signature-valid = valid ; context-valid = wf[]
  ; term-scoped = sc-ctor (st∷ sc-atom_lit (st∷ sc-float_type (st∷ sc-float_lit st[])))
  ; goal-scoped = goal-scoped ; goal-level = l1 ; goal-kind = goal-kind
  ; checked = check value-typed }

program-admitted : Admitted ⟨⟩ program tm-float_type
program-admitted = record
  { signature-valid = valid ; context-valid = wf[]
  ; term-scoped = sc-case
      (Admitted.term-scoped value-admitted) motive-scoped
      (sb∷ (sbranch (sc-var (s≤s z≤n))) (sb∷ (sbranch (sc-var (s≤s z≤n))) sb[]))
  ; goal-scoped = sc-float_type ; goal-level = l0 ; goal-kind = ⇒-float_type
  ; checked = check program-typed }

-- This is the missing base-closing premise, now INHABITED natively.
-- It does not assert the as-yet-unproved native substitution theorem.
scrutinee-context : WellFormed (extend ⟨⟩ goal)
scrutinee-context = wf∷ wf[] goal-scoped goal-kind
native-closing : ∀ (i : Fin.Fin 1)
  → ⟨⟩ ⊢ topSub value (Fin.toℕ i) ⇒ substS (topSub value) (lookup (extend ⟨⟩ goal) i)
native-closing Fin.zero = value-typed

caller : Ctx 1
caller = extend ⟨⟩ tm-atom_type
caller-wf : WellFormed caller
caller-wf = wf∷ wf[] sc-atom_type ⇒-atom_type
open-fields : List Term
open-fields = tm-var 0 ∷ tm-float_type ∷ tm-float_lit ∷ []
open-spine : Spine caller (tm-atom_type ∷ []) open-fields indices
open-spine = sp∷ (check (⇒-var Fin.zero))
  (sp∷ (check ⇒-float_type) (sp∷ (check ⇒-float_lit) sp[]))
open-value : Term
open-value = tm-ctor "NativeMk" open-fields
open-typed : caller ⊢ tm-case open-value motive-term branches ⇒ tm-float_type
open-typed = ⇒-conv
  (⇒-case caller-wf refl (⇒-ctor refl actual-parameters open-spine)
    actual-parameters open-spine motive-valid (branches-typed caller-wf) coverage)
  (motive-reduces (tm-var 0) tm-float_type tm-float_lit open-value)
