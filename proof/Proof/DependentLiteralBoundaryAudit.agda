------------------------------------------------------------------------
-- AUDIT: native declaration validity does not certify literal peeling.
-- Nat is unindexed and registered, but S's field is Float, not Nat.
-- The source is closed, final, covered and natively admitted at Float;
-- its actual compact-literal iota reduct cannot check at Float.
-- This refutes insufficient metatheory assumptions, not the kernel.
------------------------------------------------------------------------
module Proof.DependentLiteralBoundaryAudit where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (s≤s; z≤n)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l1; l≤-refl)
open import Core.Signature
open import Core.Reduction
open import Core.Coverage
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.DependentTyping
open import Proof.Progress using
  (Final; StrictlyPositive; BodiesFinal; f-case; f-nat_lit; f-lam;
   f-data; ft[]; f-float_type; f-float_lit; f-var; fb∷; fb[])
import Proof.ReductionConversion as Reduction

zero-ctor suc-ctor : Ctor
zero-ctor = record
  { ctor-name = "Z"; ctor-args = []; ctor-params = []; ctor-indices = [] }
suc-ctor = record
  { ctor-name = "S"; ctor-args = ("predecessor" , tm-float_type) ∷ []
  ; ctor-params = []; ctor-indices = [] }
family : Family
family = record
  { fam-name = "Nat"; fam-params = []; fam-indices = []
  ; fam-level = l0; fam-ctors = zero-ctor ∷ suc-ctor ∷ []
  ; positive = true; universe-ok = true }
builtin-table : Name → Maybe Name
builtin-table name with name ≟ "nat"
... | yes equal = just "Nat"
... | no different = nothing
env : IndEnv
env = record { families = family ∷ []; builtins = builtin-table }
sig : Signature
sig = record { type-of = λ _ → nothing; body = λ _ → nothing }
module R = Reduction.Model sig (λ ())
conv : Conversion
conv = R.conversion
module T = Core.DependentTyping.Typing env sig conv
open T

check : ∀ {n} {Γ : Ctx n} {t A} → Γ ⊢ t ⇒ A → Γ ⊢ t ⇐ A
check {A = A} typed = ⇐-infer typed (Conversion.≈-refl conv {t = A})
nat : Term
nat = tm-data "Nat" [] []
nat-kind : ∀ {n} {Γ : Ctx n} → Γ ⊢ nat ⇒ tm-type l0
nat-kind = ⇒-data refl sp[] sp[]
nat-scoped : ∀ {n} → Scoped n nat
nat-scoped = sc-data st[] st[]

family-declaration : FamilyDeclaration family
family-declaration = record
  { parameter-context = ⟨⟩; index-context = ⟨⟩
  ; parameters = dt[]; indices = dt[] }
zero-declaration : ConstructorDeclaration family zero-ctor
zero-declaration = record
  { parameter-context = ⟨⟩; field-context = ⟨⟩
  ; parameters = dt[]; fields = dt[]; field-levels = tt
  ; result-scoping = st[] , st[]; uniform-parameters = refl
  ; result-parameters = sp[]; result-indices = sp[] }
suc-declaration : ConstructorDeclaration family suc-ctor
suc-declaration = record
  { parameter-context = ⟨⟩; field-context = extend ⟨⟩ tm-float_type
  ; parameters = dt[]; fields = dt∷ sc-float_type ⇒-float_type dt[]
  ; field-levels = l≤-refl , tt
  ; result-scoping = st[] , st[]; uniform-parameters = refl
  ; result-parameters = sp[]; result-indices = sp[] }
family-declared : ∀ {name f}
  → findFamily name (IndEnv.families env) ≡ just f → FamilyDeclaration f
family-declared {name} found with name ≟ "Nat"
... | yes refl with just-inj found
... | refl = family-declaration
family-declared {name} () | no different
constructor-declared : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct)
  → ConstructorDeclaration f ct
constructor-declared {name} found
  with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , equal = zero-declaration
... | here refl , there (here refl) , equal = suc-declaration
... | here refl , there (there ()) , equal
... | there () , member , equal
owner-visible : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct)
  → findFamily (fam-name f) (IndEnv.families env) ≡ just f
owner-visible {name} found
  with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , member , equal = refl
... | there () , member , equal
valid : SignatureValid
valid = record
  { family-declared = λ {name} → family-declared {name}
  ; constructor-declared = λ {name} → constructor-declared {name}
  ; owner-visible = λ {name} → owner-visible {name}
  ; global-type = λ (); global-body = λ () }
signature-positive : StrictlyPositive env
signature-positive .family (here refl) = refl
signature-positive f (there ())
bodies-final : BodiesFinal sig
bodies-final ()

motive-term : Term
motive-term = tm-lam unrestricted nat tm-float_type
motive-scoped : ∀ {n} → Scoped n motive-term
motive-scoped = sc-lam nat-scoped sc-float_type
motive-valid : ∀ {n} {Γ : Ctx n} → Motive Γ family [] motive-term l0
motive-valid = motive motive-scoped
  (⇒-pi nat-kind (⇒-type refl))
  (⇒-lam nat-kind (check ⇒-float_type))
motive-reduces : ∀ s → Conversion._≈_ conv (tm-app motive-term s) tm-float_type
motive-reduces s = R.reduce-converts {t = tm-app motive-term s} β
motive-symmetric : ∀ s → Conversion._≈_ conv tm-float_type (tm-app motive-term s)
motive-symmetric s = Conversion.≈-sym conv
  {t = tm-app motive-term s} {u = tm-float_type} (motive-reduces s)
branches : List Branch
branches = ("Z" , 0 , tm-float_lit) ∷ ("S" , 1 , tm-var 0) ∷ []
fresh-wf : WellFormed (extend ⟨⟩ tm-float_type)
fresh-wf = wf∷ wf[] sc-float_type ⇒-float_type
branches-typed : Branches ⟨⟩ family [] motive-term branches
branches-typed = br∷ refl refl op[] wf[]
  (⇐-infer ⇒-float_lit (motive-symmetric (tm-ctor "Z" [])))
  (br∷ refl refl (op∷ op[]) fresh-wf
    (⇐-infer (⇒-var Fin.zero)
      (motive-symmetric (tm-ctor "S" (tm-var 0 ∷ [])))) br[])
covered-ctor : ∀ {name f ct}
  → findCtor name (IndEnv.families env) ≡ just (f , ct)
  → fam-name f ≡ "Nat" → HasBranch name (length (ctor-args ct)) branches
covered-ctor {name} found owner
  with lookup-ctor-members {c = name} {fs = IndEnv.families env} found
... | here refl , here refl , refl = tm-float_lit , refl
... | here refl , there (here refl) , refl = tm-var 0 , refl
... | here refl , there (there ()) , equal
... | there () , member , equal
coverage : CaseCoverage env "Nat" branches
coverage = record
  { ctor-covered = λ {name} → covered-ctor {name}
  ; nat-zero-covered = λ _ → tm-float_lit , refl
  ; nat-suc-covered = λ _ → tm-var 0 , refl
  ; bounded-zero-covered = λ (); bounded-suc-covered = λ () }
literal-typed : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ tm-nat_lit k ⇒ nat
literal-typed = ⇒-nat_lit refl refl refl refl
program reduct : Term
program = tm-case (tm-nat_lit 1) motive-term branches
reduct = tm-nat_lit 0
program-typed : ⟨⟩ ⊢ program ⇒ tm-float_type
program-typed = ⇒-conv
  (⇒-case wf[] refl literal-typed sp[] sp[] motive-valid branches-typed coverage)
  (motive-reduces (tm-nat_lit 1))
program-checks : ⟨⟩ ⊢ program ⇐ tm-float_type
program-checks = check program-typed
program-admitted : Admitted ⟨⟩ program tm-float_type
program-admitted = record
  { signature-valid = valid; context-valid = wf[]
  ; term-scoped = sc-case sc-nat_lit motive-scoped
      (sb∷ (sbranch sc-float_lit) (sb∷ (sbranch (sc-var (s≤s z≤n))) sb[]))
  ; goal-scoped = sc-float_type; goal-level = l0; goal-kind = ⇒-float_type
  ; checked = program-checks }
program-final : Final program
program-final = f-case f-nat_lit (f-lam (f-data ft[] ft[]) f-float_type)
  (fb∷ f-float_lit (fb∷ f-var fb[]))
reduct-final : Final reduct
reduct-final = f-nat_lit
program-step : _⇝_ sig program reduct
program-step = ι-nat-suc refl refl

-- Parametric and opaque so the inversion does not unfold the full model.
-- Every native conversion/cumulativity wrapper is handled explicitly.
module LiteralInversion (c : Conversion) where
  module N = Core.DependentTyping.Typing env sig c
  abstract
    eq : (A : Term) → Conversion._≈_ c A A
    eq A = Conversion.≈-refl c {t = A}
    compose : ∀ A B C → Conversion._≈_ c A B
      → Conversion._≈_ c B C → Conversion._≈_ c A C
    compose A B C = Conversion.≈-trans c {t = A} {u = B} {v = C}
    nat-not-sort : ∀ {l} → Conversion._≈_ c nat (tm-type l) → ⊥
    nat-not-sort {l} equal with Conversion.≈-heads c
      {t = nat} {u = tm-type l} ty-data ty-universe equal
    ... | ()
    nat-not-float : Conversion._≈_ c nat tm-float_type → ⊥
    nat-not-float equal with Conversion.≈-heads c
      {t = nat} {u = tm-float_type} ty-data ty-float equal
    ... | ()
    nat-inference : ∀ {n} {Γ : Ctx n} {k A}
      → N._⊢_⇒_ Γ (tm-nat_lit k) A → Conversion._≈_ c nat A
    nat-inference (N.⇒-nat_lit builtin found ps is) with just-inj builtin
    ... | refl = eq nat
    nat-inference {A = A} (N.⇒-conv {T = B} typed equal) =
      compose nat B A (nat-inference typed) equal
    nat-inference (N.⇒-cumul typed le) = ⊥-elim (nat-not-sort (nat-inference typed))
    nat-checking : ∀ {n} {Γ : Ctx n} {k A}
      → N._⊢_⇐_ Γ (tm-nat_lit k) A → Conversion._≈_ c nat A
    nat-checking {A = A} (N.⇐-infer {T′ = B} typed equal) =
      compose nat B A (nat-inference typed) equal
    nat-checking {A = A} (N.⇐-conv {T = B} typed equal) =
      compose nat B A (nat-checking typed) equal
    nat-checking (N.⇐-cumul typed le) = ⊥-elim (nat-not-sort (nat-inference typed))

module I = LiteralInversion conv
reduct-not-checks : ⟨⟩ ⊢ reduct ⇐ tm-float_type → ⊥
reduct-not-checks typed = I.nat-not-float (I.nat-checking typed)
reduct-not-infers : ⟨⟩ ⊢ reduct ⇒ tm-float_type → ⊥
reduct-not-infers typed = I.nat-not-float (I.nat-inference typed)

-- Even the weaker, closed/final/valid-signature formulation is false.
literal-preservation-refuted :
  (SignatureValid → WellFormed ⟨⟩ → Final program
    → ⟨⟩ ⊢ program ⇐ tm-float_type → _⇝_ sig program reduct
    → ⟨⟩ ⊢ reduct ⇐ tm-float_type) → ⊥
literal-preservation-refuted preserve =
  reduct-not-checks (preserve valid wf[] program-final program-checks program-step)
