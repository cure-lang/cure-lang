------------------------------------------------------------------------
-- Local coverage is inhabited, rejects missing/wrong branches, and is
-- carried by actual case typing. No global Covers/ClosedSig/ReduceConv
-- premise is used. The final typing refutation is parameterised by the
-- abstract Conversion interface, not a full soundness-model instance.
------------------------------------------------------------------------
module Proof.CoverageExamples where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Coverage
open import Core.Typing using (Conversion; ⟨⟩)
open import Proof.Inversion using (module Invert)

nat-type : Term
nat-type = tm-data "Nat" [] []

z : Ctor
z = record { ctor-name = "Z" ; ctor-args = [] ; ctor-params = [] ; ctor-indices = [] }

s : Ctor
s = record
  { ctor-name = "S" ; ctor-args = ("_" , nat-type) ∷ []
  ; ctor-params = [] ; ctor-indices = [] }

false-ctor : Ctor
false-ctor = record { ctor-name = "False" ; ctor-args = [] ; ctor-params = [] ; ctor-indices = [] }

true-ctor : Ctor
true-ctor = record { ctor-name = "True" ; ctor-args = [] ; ctor-params = [] ; ctor-indices = [] }

nat-family : Family
nat-family = record
  { fam-name = "Nat" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = z ∷ s ∷ [] ; universe-ok = true ; positive = true }

bool-family : Family
bool-family = record
  { fam-name = "Bool" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = false-ctor ∷ true-ctor ∷ [] ; universe-ok = true ; positive = true }

void-family : Family
void-family = record
  { fam-name = "Void" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = [] ; universe-ok = true ; positive = true }

-- A partial builtin environment: Nat is registered; Bool is an ordinary
-- unrelated family and Void is empty. No Bounded builtin is registered.
builtin-name : Name → Maybe Name
builtin-name "nat" = just "Nat"
builtin-name _ = nothing

env : IndEnv
env = record { families = nat-family ∷ bool-family ∷ void-family ∷ []
             ; builtins = builtin-name }

sig : Signature
sig = record { body = λ _ → nothing ; type-of = λ _ → nothing }

branch-let : Term
branch-let = tm-let unrestricted nat-type (tm-var 0) (tm-var 0)

nat-branches : List Branch
nat-branches = ("Z" , 0 , tm-nat_lit 7) ∷ ("S" , 1 , branch-let) ∷ []

nat-constructors : ∀ {c f ct}
  → findCtor c (IndEnv.families env) ≡ just (f , ct)
  → fam-name f ≡ "Nat"
  → HasBranch c (length (ctor-args ct)) nat-branches
nat-constructors {c} {f} {ct} found owner
  with lookup-ctor-members {c = c} {fs = IndEnv.families env} {f = f} {ct = ct} found
... | here refl , here refl , refl = tm-nat_lit 7 , refl
... | here refl , there (here refl) , refl = branch-let , refl
... | here refl , there (there ()) , name
nat-constructors found () | there (here refl) , member , name
nat-constructors found owner | there (there (here refl)) , () , name
nat-constructors found owner | there (there (there ())) , member , name

nat-covered : CaseCoverage env "Nat" nat-branches
nat-covered = record
  { ctor-covered = nat-constructors
  ; nat-zero-covered = λ _ → tm-nat_lit 7 , refl
  ; nat-suc-covered = λ _ → branch-let , refl
  ; bounded-zero-covered = λ ()
  ; bounded-suc-covered = λ ()
  }

-- Unrelated Bool constructors are present but not required by a Nat case.
true-is-present :
  findCtor "True" (IndEnv.families env) ≡ just (bool-family , true-ctor)
true-is-present = refl

no-unrelated-branch : HasBranch "True" 0 nat-branches → ⊥
no-unrelated-branch (body , ())

missing-nat-rejected : CaseCoverage env "Nat" [] → ⊥
missing-nat-rejected covered with nat-zero-covered covered refl
... | body , ()

missing-ordinary-ctor-rejected : CaseCoverage env "Bool" [] → ⊥
missing-ordinary-ctor-rejected covered
  with ctor-covered covered {c = "True"} {f = bool-family} {ct = true-ctor} refl refl
... | body , ()

wrong-arity-rejected :
  CaseCoverage env "Nat" (("Z" , 1 , tm-nat_lit 7) ∷ ("S" , 1 , branch-let) ∷ []) → ⊥
wrong-arity-rejected covered with nat-zero-covered covered refl
... | body , ()

-- findBranch is first-match: a later correct duplicate does not repair
-- the wrong arity of the branch the evaluator would actually select.
wrong-first-duplicate-rejected :
  CaseCoverage env "Nat" (("Z" , 1 , tm-nat_lit 7) ∷ nat-branches) → ⊥
wrong-first-duplicate-rejected covered with nat-zero-covered covered refl
... | body , ()

void-constructors : ∀ {c f ct}
  → findCtor c (IndEnv.families env) ≡ just (f , ct)
  → fam-name f ≡ "Void" → HasBranch c (length (ctor-args ct)) []
void-constructors {c} {f} {ct} found owner
  with lookup-ctor-members {c = c} {fs = IndEnv.families env} {f = f} {ct = ct} found
void-constructors found () | here refl , member , name
void-constructors found () | there (here refl) , member , name
void-constructors found owner | there (there (here refl)) , () , name
void-constructors found owner | there (there (there ())) , member , name

empty-elimination-covered : CaseCoverage env "Void" []
empty-elimination-covered = record
  { ctor-covered = void-constructors
  ; nat-zero-covered = λ ()
  ; nat-suc-covered = λ ()
  ; bounded-zero-covered = λ ()
  ; bounded-suc-covered = λ ()
  }

renamed-covered : CaseCoverage env "Nat" (renameBranches wk nat-branches)
renamed-covered = case-coverage-rename wk nat-covered

substituted-covered :
  CaseCoverage env "Nat" (substBranchesS (topSub (tm-nat_lit 99)) nat-branches)
substituted-covered = case-coverage-subst (topSub (tm-nat_lit 99)) nat-covered

reduced-branches : List Branch
reduced-branches = ("Z" , 0 , tm-nat_lit 7) ∷ ("S" , 1 , tm-var 0) ∷ []

branches-reduce : _⇝*ᵇ_ sig nat-branches reduced-branches
branches-reduce = ⇝ᵇ-cons ⇝*-refl (⇝ᵇ-cons (⇝*-step ζ ⇝*-refl) ⇝ᵇ-nil)

reduced-covered : CaseCoverage env "Nat" reduced-branches
reduced-covered = case-coverage-reduce sig branches-reduce nat-covered

-- This refutation inspects actual inference derivations, including
-- ⇒-conv wrappers. No assumption about all possible branch lists appears.
module TypingChecks (conv : Conversion) where
  open Core.Typing.Typing env sig conv
  open Invert env sig conv using (nat-data-family)

  nat-family-from-typing : ∀ {k n ps is}
    → ⟨⟩ ⊢ tm-nat_lit k ⇒ tm-data n ps is
    → IndEnv.builtins env "nat" ≡ just n
  nat-family-from-typing = nat-data-family

  missing-case : Term
  missing-case = tm-case (tm-nat_lit 0) (tm-lam unrestricted nat-type nat-type) []

  missing-case-not-typable : ∀ {T} → ⟨⟩ ⊢ missing-case ⇒ T → ⊥
  missing-case-not-typable (⇒-case ds dm branches covered)
    with nat-zero-covered covered (nat-family-from-typing ds)
  ... | body , ()
  missing-case-not-typable (⇒-conv der eq) = missing-case-not-typable der
  missing-case-not-typable (⇒-cumul der le) = missing-case-not-typable der
