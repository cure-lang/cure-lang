------------------------------------------------------------------------
-- Native proof certificates for the EXACT exported/replayed snapshot.
-- Proof objects are checked by Agda, not inferred from Elixir acceptance.
------------------------------------------------------------------------
module Proof.NativeCertificateExamples where

open import Data.List using (List; []; _∷_; length)
import Data.List as List
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (z≤n; s≤s)
import Data.Fin as Fin
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Coverage
open import Core.Reduction
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l≤-refl; l0≤l1)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion; a2[]; a2∷)
import Core.DependentTyping as Native
import Core.ExecutableSnapshot as Input
import Core.NativeCertificate as Certificate
import Core.CanonicalSnapshot as S
import Proof.ExecutableSnapshotExamples as E
import Fixtures.ExecutableSnapshot as Fixture
open import Proof.Substitution using (topSub-rename)

conv : Conversion
conv = E.ConversionModel.conversion
module C = Certificate.Certificates Fixture.source E.accepted E.replayed conv
module N = C.N
open N
open S.Snapshot E.snapshot public using (ind; sig)

family : Family
family = E.packed
pack alternate : Ctor
pack = E.pack
alternate = Input.ConstructorInput.declaration
  (List.lookup (Input.FamilyInput.constructors E.raw-family) (Fin.suc Fin.zero))
family-found : findFamily "Boundary#Packed" (IndEnv.families ind) ≡ just family
family-found = E.family-lookup
pack-found : findCtor "Boundary#Pack" (IndEnv.families ind) ≡ just (family , pack)
pack-found = E.ctor-lookup
alternate-found : findCtor "Boundary#Alternate" (IndEnv.families ind) ≡ just (family , alternate)
alternate-found = refl

check : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Γ ⊢ t ⇐ T
check {T = T} typed = ⇐-infer typed (Conversion.≈-refl conv {t = T})
Π : Ctx 1
Π = extend ⟨⟩ (tm-type l0)
Φ : Ctx 2
Φ = extend Π (tm-var 0)
fields-declared : Declared ⟨⟩ (ctor-args pack) Φ
fields-declared = dt∷ sc-type (⇒-type refl)
  (dt∷ (sc-var (s≤s z≤n)) (⇒-var Fin.zero) dt[])
family-declaration : FamilyDeclaration family
family-declaration = record
  { parameter-context = ⟨⟩ ; index-context = Π ; parameters = dt[]
  ; indices = dt∷ sc-type (⇒-type refl) dt[] }
pack-declaration : ConstructorDeclaration family pack
pack-declaration = record
  { parameter-context = ⟨⟩ ; field-context = Φ ; parameters = dt[]
  ; fields = fields-declared ; field-levels = l≤-refl , l0≤l1 , tt
  ; result-scoping = st[] , st∷ (sc-var (s≤s (s≤s z≤n))) st[]
  ; uniform-parameters = refl ; result-parameters = sp[]
  ; result-indices = sp∷ (check (⇒-var (Fin.suc Fin.zero))) sp[] }
computed-index : Term
computed-index = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) (tm-var 1)
computed-index-typed : Φ ⊢ computed-index ⇒ tm-type l0
computed-index-typed = ⇒-app
  (⇒-lam {c = tm-type l0} (⇒-type refl) (check (⇒-var Fin.zero))) (⇒-var (Fin.suc Fin.zero))
alternate-declaration : ConstructorDeclaration family alternate
alternate-declaration = record
  { parameter-context = ⟨⟩ ; field-context = Φ ; parameters = dt[]
  ; fields = fields-declared ; field-levels = l≤-refl , l0≤l1 , tt
  ; result-scoping = st[] ,
      st∷ (sc-app (sc-lam sc-type (sc-var (s≤s z≤n))) (sc-var (s≤s (s≤s z≤n)))) st[]
  ; uniform-parameters = refl ; result-parameters = sp[]
  ; result-indices = sp∷ (check computed-index-typed) sp[] }

goal value motive-term program : Term
goal = tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])
value = tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
motive-term = tm-lam unrestricted (tm-type l0)
  (tm-lam unrestricted (tm-data "Boundary#Packed" [] (tm-var 0 ∷ [])) (tm-var 1))
branches : List Branch
branches = ("Boundary#Pack" , 2 , tm-var 0) ∷ ("Boundary#Alternate" , 2 , tm-var 0) ∷ []
program = tm-case value motive-term branches
goal-kind : ⟨⟩ ⊢ goal ⇒ tm-type l1
goal-kind = ⇒-data family-found sp[] (sp∷ (check ⇒-atom_type) sp[])
value-typed : ⟨⟩ ⊢ value ⇒ goal
value-typed = ⇒-ctor pack-found sp[]
  (sp∷ (check ⇒-atom_type) (sp∷ (check ⇒-atom_lit) sp[]))

computed-value : Term
computed-value = tm-ctor "Boundary#Alternate" (tm-atom_type ∷ tm-atom_lit "payload" ∷ [])
computed-value-typed : ⟨⟩ ⊢ computed-value ⇒ goal
computed-value-typed = ⇒-conv
  (⇒-ctor alternate-found sp[] (sp∷ (check ⇒-atom_type) (sp∷ (check ⇒-atom_lit) sp[])))
  (Conversion.≈-data conv {n = "Boundary#Packed"} {ps = []} {ps′ = []}
    {is = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-atom_type ∷ []}
    {is′ = tm-atom_type ∷ []} a2[]
    (a2∷ (E.ConversionModel.reduce-converts
      {t = tm-app (tm-lam unrestricted (tm-type l0) (tm-var 0)) tm-atom_type} {u = tm-atom_type} β) a2[]))

path-converts : ∀ {t u} → _⇝*_ sig t u → Conversion._≈_ conv t u
path-converts {t} ⇝*-refl = Conversion.≈-refl conv {t = t}
path-converts {t} {u} (⇝*-step {u = middle} step rest) =
  Conversion.≈-trans conv {t = t} {u = middle} {v = u}
    (E.ConversionModel.reduce-converts {t = t} {u = middle} step)
    (path-converts {t = middle} {u = u} rest)
motive-path : ∀ A s → _⇝*_ sig (Native.apps motive-term (A ∷ s ∷ []))
  (substTopT s (rename wk A))
motive-path A s = ⇝*-step (ξ-app₁ β) (⇝*-step β ⇝*-refl)
motive-reduces : ∀ A s → Conversion._≈_ conv (Native.apps motive-term (A ∷ s ∷ [])) A
motive-reduces A s = subst
  (λ T → Conversion._≈_ conv (Native.apps motive-term (A ∷ s ∷ [])) T)
  (topSub-rename s A)
  (path-converts {t = Native.apps motive-term (A ∷ s ∷ [])}
    {u = substTopT s (rename wk A)} (motive-path A s))

motive-kind : ⟨⟩ ⊢ Native.motiveType family [] l0 ⇒ tm-type l1
motive-kind = ⇒-pi (⇒-type refl)
  (⇒-pi (⇒-data family-found sp[] (sp∷ (check (⇒-var Fin.zero)) sp[])) (⇒-type refl))
motive-typed : ⟨⟩ ⊢ motive-term ⇒ Native.motiveType family [] l0
motive-typed = ⇒-lam (⇒-type refl)
  (⇐-lam (⇒-data family-found sp[] (sp∷ (check (⇒-var Fin.zero)) sp[]))
    (check (⇒-var (Fin.suc Fin.zero))))
fresh-context : WellFormed Φ
fresh-context = wf∷ (wf∷ wf[] sc-type (⇒-type refl)) (sc-var (s≤s z≤n)) (⇒-var Fin.zero)
pack-goal-converts : Conversion._≈_ conv
  (Native.branchGoal "Boundary#Pack" [] pack motive-term) (tm-var 1)
pack-goal-converts = motive-reduces (tm-var 1)
  (tm-ctor "Boundary#Pack" (tm-var 1 ∷ tm-var 0 ∷ []))
alternate-goal-converts : Conversion._≈_ conv
  (Native.branchGoal "Boundary#Alternate" [] alternate motive-term) (tm-var 1)
alternate-goal-converts = Conversion.≈-trans conv
  {t = Native.branchGoal "Boundary#Alternate" [] alternate motive-term}
  {u = computed-index} {v = tm-var 1}
  (motive-reduces computed-index (tm-ctor "Boundary#Alternate" (tm-var 1 ∷ tm-var 0 ∷ [])))
  (E.ConversionModel.reduce-converts {t = computed-index} {u = tm-var 1} β)
branches-typed : Branches ⟨⟩ family [] motive-term branches
branches-typed = br∷ pack-found refl (Native.op∷ (Native.op∷ Native.op[])) fresh-context
  (⇐-infer (⇒-var Fin.zero) (Conversion.≈-sym conv
    {t = Native.branchGoal "Boundary#Pack" [] pack motive-term} {u = tm-var 1} pack-goal-converts))
  (br∷ alternate-found refl (Native.op∷ (Native.op∷ Native.op[])) fresh-context
    (⇐-infer (⇒-var Fin.zero) (Conversion.≈-sym conv
      {t = Native.branchGoal "Boundary#Alternate" [] alternate motive-term}
      {u = tm-var 1} alternate-goal-converts)) br[])

covered : ∀ {name f ct} → findCtor name (IndEnv.families ind) ≡ just (f , ct)
  → fam-name f ≡ "Boundary#Packed" → HasBranch name (length (ctor-args ct)) branches
covered {name} found owner with lookup-ctor-members {c = name} {fs = IndEnv.families ind} found
... | here refl , here refl , refl = tm-var 0 , refl
... | here refl , there (here refl) , refl = tm-var 0 , refl
... | here refl , there (there ()) , equal
... | there () , member , equal
coverage : CaseCoverage ind "Boundary#Packed" branches
coverage = record
  { ctor-covered = λ {name} → covered {name}
  ; nat-zero-covered = λ () ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ () ; bounded-suc-covered = λ () }
program-typed : ⟨⟩ ⊢ program ⇒ tm-atom_type
program-typed = ⇒-conv
  (⇒-case wf[] family-found value-typed sp[] (sp∷ (check ⇒-atom_type) sp[])
    (motive (E.B.scoped E.motive-supported) motive-kind motive-typed) branches-typed coverage)
  (motive-reduces tm-atom_type value)

computed-program : Term
computed-program = tm-case computed-value motive-term branches
computed-program-typed : ⟨⟩ ⊢ computed-program ⇒ tm-atom_type
computed-program-typed = ⇒-conv
  (⇒-case wf[] family-found computed-value-typed sp[] (sp∷ (check ⇒-atom_type) sp[])
    (motive (E.B.scoped E.motive-supported) motive-kind motive-typed) branches-typed coverage)
  (motive-reduces tm-atom_type computed-value)

evidence : C.Evidence
evidence = record
  { families = record
      { declaration = family-declaration
      ; constructors = pack-declaration All.∷ alternate-declaration All.∷ All.[] } All.∷ All.[]
  ; definitions =
      record { level = l0 ; kind = ⇒-atom_type ; body = ⇒-atom_lit } All.∷
      record { level = l0 ; kind = ⇒-atom_type ; body = ⇒-atom_lit } All.∷
      record { level = l1 ; kind = goal-kind ; body = value-typed } All.∷
      record { level = l0 ; kind = ⇒-atom_type ; body = program-typed } All.∷ All.[] }
valid : SignatureValid
valid = C.validity evidence
program-admitted : Admitted ⟨⟩ program tm-atom_type
program-admitted = C.admitted evidence {entry = E.raw-unpack}
  (there (there (there (here refl)))) refl
program-eligible : C.A.Eligible ⟨⟩ program tm-atom_type
program-eligible = C.eligible evidence {entry = E.raw-unpack}
  (there (there (there (here refl)))) refl
hidden-held-admitted : Admitted ⟨⟩ (tm-atom_lit "hidden") tm-atom_type
hidden-held-admitted = C.admitted evidence {entry = E.raw-held} (there (here refl)) refl
