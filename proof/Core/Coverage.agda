------------------------------------------------------------------------
-- Coverage belongs to ONE admitted case, not every raw branch list.
--
-- This first interface conservatively requires all constructors of the
-- scrutinee's family. Indexed impossible-branch omission is not modelled.
-- Compact builtin literals require their canonical branch names/arities
-- only when the scrutinee family has the corresponding builtin identity.
------------------------------------------------------------------------
module Core.Coverage where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Core.Syntax
open import Core.Signature
open import Core.Reduction

lookup-ctor-members : ∀ {c fs f ct}
  → findCtor c fs ≡ just (f , ct)
  → f ∈ fs × ct ∈ fam-ctors f × c ≡ ctor-name ct
lookup-ctor-members {fs = []} ()
lookup-ctor-members {c} {f₀ ∷ fs} found
  with findCtorIn c (fam-ctors f₀) in entry
... | just ct₀ with just-inj found
... | refl = here refl , findCtorIn-∈ {cs = fam-ctors f₀} entry
                       , findCtorIn-sound {cs = fam-ctors f₀} entry
lookup-ctor-members {c} {f₀ ∷ fs} found | nothing
  with lookup-ctor-members {fs = fs} found
... | member , ctor-member , name = there member , ctor-member , name

HasBranch : Name → ℕ → List Branch → Set
HasBranch c ar brs = ∃ λ b → findBranch c brs ≡ just (c , ar , b)

record CaseCoverage (ind : IndEnv) (family : Name) (brs : List Branch) : Set where
  field
    ctor-covered : ∀ {c f ct}
      → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      → fam-name f ≡ family
      → HasBranch c (length (ctor-args ct)) brs
    nat-zero-covered : IndEnv.builtins ind "nat" ≡ just family → HasBranch "Z" 0 brs
    nat-suc-covered : IndEnv.builtins ind "nat" ≡ just family → HasBranch "S" 1 brs
    bounded-zero-covered : IndEnv.builtins ind "bounded" ≡ just family → HasBranch "First" 1 brs
    bounded-suc-covered : IndEnv.builtins ind "bounded" ≡ just family → HasBranch "Next" 2 brs

open CaseCoverage public

has-branch-rename : ∀ ρ c ar {brs}
  → HasBranch c ar brs → HasBranch c ar (renameBranches ρ brs)
has-branch-rename ρ c ar {brs} (b , found) =
  _ , findBranch-rename ρ c brs found

has-branch-subst : ∀ σ c ar {brs}
  → HasBranch c ar brs → HasBranch c ar (substBranchesS σ brs)
has-branch-subst σ c ar {brs} (b , found) =
  _ , findBranch-substBranchesS σ c brs found

case-coverage-rename : ∀ {ind family brs} ρ
  → CaseCoverage ind family brs → CaseCoverage ind family (renameBranches ρ brs)
case-coverage-rename {brs = brs} ρ covered = record
  { ctor-covered = λ fc owner → has-branch-rename ρ _ _ {brs = brs} (ctor-covered covered fc owner)
  ; nat-zero-covered = λ eq → has-branch-rename ρ "Z" 0 {brs = brs} (nat-zero-covered covered eq)
  ; nat-suc-covered = λ eq → has-branch-rename ρ "S" 1 {brs = brs} (nat-suc-covered covered eq)
  ; bounded-zero-covered = λ eq → has-branch-rename ρ "First" 1 {brs = brs} (bounded-zero-covered covered eq)
  ; bounded-suc-covered = λ eq → has-branch-rename ρ "Next" 2 {brs = brs} (bounded-suc-covered covered eq)
  }

case-coverage-subst : ∀ {ind family brs} σ
  → CaseCoverage ind family brs → CaseCoverage ind family (substBranchesS σ brs)
case-coverage-subst {brs = brs} σ covered = record
  { ctor-covered = λ fc owner → has-branch-subst σ _ _ {brs = brs} (ctor-covered covered fc owner)
  ; nat-zero-covered = λ eq → has-branch-subst σ "Z" 0 {brs = brs} (nat-zero-covered covered eq)
  ; nat-suc-covered = λ eq → has-branch-subst σ "S" 1 {brs = brs} (nat-suc-covered covered eq)
  ; bounded-zero-covered = λ eq → has-branch-subst σ "First" 1 {brs = brs} (bounded-zero-covered covered eq)
  ; bounded-suc-covered = λ eq → has-branch-subst σ "Next" 2 {brs = brs} (bounded-suc-covered covered eq)
  }

-- Branch-body reduction preserves both the first-match name and its arity.
has-branch-reduce : ∀ sig c ar {brs brs′}
  → _⇝*ᵇ_ sig brs brs′ → HasBranch c ar brs → HasBranch c ar brs′
has-branch-reduce sig c ar ⇝ᵇ-nil (b , ())
has-branch-reduce sig c ar
  (⇝ᵇ-cons {cn = cn} {b′ = b′} body rest) (b , found) with c ≟ cn
... | yes refl =
  b′ , cong (λ q → just (c , proj₁ (proj₂ q) , b′)) (just-inj found)
... | no neq = has-branch-reduce sig c ar rest (b , found)

case-coverage-reduce : ∀ sig {ind family brs brs′}
  → _⇝*ᵇ_ sig brs brs′ → CaseCoverage ind family brs → CaseCoverage ind family brs′
case-coverage-reduce sig steps covered = record
  { ctor-covered = λ fc owner → has-branch-reduce sig _ _ steps (ctor-covered covered fc owner)
  ; nat-zero-covered = λ eq → has-branch-reduce sig "Z" 0 steps (nat-zero-covered covered eq)
  ; nat-suc-covered = λ eq → has-branch-reduce sig "S" 1 steps (nat-suc-covered covered eq)
  ; bounded-zero-covered = λ eq → has-branch-reduce sig "First" 1 steps (bounded-zero-covered covered eq)
  ; bounded-suc-covered = λ eq → has-branch-reduce sig "Next" 2 steps (bounded-suc-covered covered eq)
  }
