------------------------------------------------------------------------
-- The dynamic semantics: the reduction relation ⇝.
--
-- This is the SPECIFICATION of Core evaluation, not the NbE implementation.
-- docs/SOUNDNESS.md §1.3 names four rules:
--
--   β: (λx. b) a ⇝ b[x := a]
--   ζ: let x = v in b ⇝ b[x := v]
--   ι: case (ctor c args) of … ⇝ b_c[args]
--   δ: global f ⇝ body(f)   — GATED on a totality certificate
--
-- We define ⇝ as an inductive family (a small-step relation), which is what
-- Progress and Preservation are stated over. Modelling the relation rather
-- than the NbE function sidesteps the termination obligations of a total
-- evaluator (the kernel's own `Eval` is partial by design: it can raise on
-- ill-typed terms) and matches the theorem statement exactly.
--
-- Congruence (reduction under a context) is given by the `ξ-*` rules, which
-- mirror where the kernel forces subterms: tm-app` forces the function
-- position, tm-case` forces the scrutinee, and the inert effect nodes force
-- their subterms structurally.
------------------------------------------------------------------------
module Core.Reduction where

open import Data.Bool using (Bool; true; false)
open import Data.String.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; length; map; find; reverse; updateAt)
open import Data.List using () renaming (lookup to listLookup)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Syntax
open import Core.Signature using (just-inj)

------------------------------------------------------------------------
-- Substituting a list of constructor arguments into a branch body.
--
-- The branch binds `arity` fields; `args` are the fields in surface order.
-- The LAST field is de Bruijn 0 (matching `Eval.reduce_branch_body`, which
-- binds `reverse(fields) ++ base_env`). This is a SIMULTANEOUS substitution
-- (`substS`), the presentation used throughout the development: field i
-- (counting the last as 0) replaces de Bruijn index i, and indices above the
-- fields are left unchanged.
--
-- The simultaneous form is not merely stylistic here: the former targeted
-- definition (`substT` composed field-by-field) applied the substitutions in
-- sequence, so a later `substT` could capture an earlier field inserted under
-- a binder. One simultaneous substitution inserts every field at once, so no
-- field is re-scanned — matching the kernel's single `eval(body, reverse
-- fields ++ base_env)`.
------------------------------------------------------------------------
-- The simultaneous substitution of a branch's fields: `args` in surface
-- order, the FIRST field at index 0 (matching `branch-field-vars ar =
-- [0, …, ar-1]` and the branch context `extendTele Γ (ctor-args ct)`, whose
-- FIRST telescope entry is innermost). Indices at or above the field count
-- are fixed.
-- The worker is exposed at the top level (rather than `where`-bound) so the
-- metatheory can reason about the shape of `argsSub`'s images: the first
-- `length args` indices map to the fields, the rest to variables.
argsSub-go : ℕ → List Term → Sub
argsSub-go k [] i = tm-var i
argsSub-go k (a ∷ as) zero = a
argsSub-go k (a ∷ as) (suc i) = argsSub-go (suc k) as i

argsSub : List Term → Sub
argsSub args = argsSub-go 0 args

-- `argsSub-go` on a base-environment index (at or above the field count) is
-- the identity: `argsSub-go k ys (length ys + i) ≡ tm-var i`.
argsSub-go-raise : ∀ k (ys : List Term) i → argsSub-go k ys (length ys + i) ≡ tm-var i
argsSub-go-raise k [] i = refl
argsSub-go-raise k (y ∷ ys) i = argsSub-go-raise (suc k) ys i

-- `argsSub-go` on a FIELD index (below the field count) is the field.
argsSub-go-field : ∀ k (ys : List Term) (i : Fin (length ys))
  → argsSub-go k ys (toℕ i) ≡ listLookup ys i
argsSub-go-field k (y ∷ ys) zero = refl
argsSub-go-field k (y ∷ ys) (suc i) = argsSub-go-field (suc k) ys i

substArgs : List Term → Term → Term
substArgs args b = substS (argsSub args) b

------------------------------------------------------------------------
-- The δ-table: a signature mapping certified global names to their bodies.
--
-- The kernel gates δ on a totality certificate (`Env.certified?`). We
-- model the certified fragment as a finite map from names to bodies; a
-- name NOT in the map is an opaque global that never unfolds (it reduces
-- to a neutral, per `Eval.eval({:global, name})`).
--
-- This is the single hypothesis the whole soundness argument rests on
-- (docs/SOUNDNESS.md §5.3(2), §7.2): we will later attach the *property*
-- that every body in this table terminates, but Progress/Preservation
-- only need the table to be well-typed (Preservation §4, δ case).
------------------------------------------------------------------------

record Signature : Set where
  field
    body : Name → Maybe Term
    -- The declared type of each global (for the δ Preservation case).
    type-of : Name → Maybe Term

open Signature public

------------------------------------------------------------------------
findBranch : Name → List Branch → Maybe Branch
findBranch c [] = nothing
findBranch c ((cn , ar , b) ∷ xs) with c ≟ cn
... | yes refl = just (c , ar , b)
... | no _     = findBranch c xs

-- `findBranch` is COMPLETE: if a branch named `c` is in the list, the lookup
-- finds a branch named `c`. Used by Progress's `case`/ι case to turn the
-- coverage witness (`Covers`) into the `findBranch c brs ≡ just (c , ar , b)`
-- premise of the ι rule.
findBranch-complete : ∀ c brs {ar b}
                    → (c , ar , b) ∈ brs
                    → ∃ λ ar′ → ∃ λ b′ → findBranch c brs ≡ just (c , ar′ , b′)
findBranch-complete c ((cn , ar , b) ∷ xs) (here refl) with c ≟ cn
... | yes refl = _ , _ , refl
... | no ¬q = ⊥-elim (¬q refl)
findBranch-complete c ((cn , ar , b) ∷ xs) (there p) with c ≟ cn
... | yes refl = _ , _ , refl
... | no _     = findBranch-complete c xs p

-- `findBranch` is SOUND: it only returns branches that are in the list.
findBranch-sound : ∀ c brs {ar b} → findBranch c brs ≡ just (c , ar , b) → (c , ar , b) ∈ brs
findBranch-sound c [] ()
findBranch-sound c ((cn , ar′ , b′) ∷ xs) {ar} {b} eq with c ≟ cn
... | yes refl = subst (λ q → q ∈ ((c , ar′ , b′) ∷ xs)) (just-inj eq) (here refl)
... | no _     = there (findBranch-sound c xs eq)
------------------------------------------------------------------------
-- The reduction relation, parameterised by the signature.
------------------------------------------------------------------------

module _ (sig : Signature) where

  infix 4 _⇝_

  mutual

    data _⇝_ : Term → Term → Set where

      -- β: (λx. b) a ⇝ b[x := a]
      --
      -- The substitution is the TOP substitution `substTopT a b = substS
      -- (topSub a) b`, matching the kernel's `Eval.apply_closure`, which
      -- evaluates the body in the environment `[a_value | env]` (prepend
      -- the argument at index 0, shift everything else).
      --
      -- The ARGUMENT must be a VALUE: the kernel's β fires only on
      -- `apply(vlam, varg)`, and the `ξ-app₂` congruence reduces the
      -- argument to a value first. Requiring `Value a` is what makes the β
      -- case of Preservation go through: a value of a type INFERS that
      -- type (`value-infer`), which is what the substitution lemma's head
      -- case needs (the argument is only CHECKED by `⇒-app`).
      β : ∀ {g d b a} → Value a → tm-app (tm-lam g d b) a ⇝ substTopT a b

      -- ζ: let x = v in b ⇝ b[x := v]. The bound value must likewise be a
      -- value (the kernel's `let` is ζ-transparent and its value is a
      -- value).
      ζ : ∀ {g ty v b} → Value v → tm-let g ty v b ⇝ substTopT v b

      -- ι: case (ctor c args) of … ⇝ b_c[args]
      -- The branch body lives under `arity` binders; we substitute the fields
      -- in left-to-right, innermost last, matching `Eval.reduce_branch_body`.
      ι : ∀ {m brs c ar b args}
        → findBranch c brs ≡ just (c , ar , b)
        → length args ≡ ar
        → tm-case (tm-ctor c args) m brs ⇝ substArgs args b

      -- ι-nat / ι-bounded: a COMPACT builtin literal scrutinee peels ONE layer
      -- to its constructor form and reuses the ι rule above, exactly as the
      -- kernel's `Eval.nat_to_ctor_if` / `bounded_to_ctor_if` do at each ι-site.
      --
      --   nat_lit 0     ≙ Z            (0 args)
      --   nat_lit (n+1) ≙ S(nat_lit n) (1 arg, predecessor left compact)
      --   bounded_lit 0     ≙ First(nat_lit 0)                (1 arg: the bound)
      --   bounded_lit (k+1) ≙ Next(nat_lit k, bounded_lit k)  (2 args: bound, pred)
      --
      -- The constructor names are the builtin basenames (`Z`/`S`/`First`/`Next`),
      -- matching the kernel's `@builtin_ctor_aliases`; the metatheory uses the
      -- basename directly rather than the owner-qualified identity.
      ι-nat-zero : ∀ {m brs ar b}
        → findBranch "Z" brs ≡ just ("Z" , ar , b)
        → tm-case (tm-nat_lit 0) m brs ⇝ substArgs [] b

      ι-nat-suc : ∀ {m brs ar b n}
        → findBranch "S" brs ≡ just ("S" , ar , b)
        → tm-case (tm-nat_lit (suc n)) m brs ⇝ substArgs (tm-nat_lit n ∷ []) b

      ι-bounded-zero : ∀ {m brs ar b}
        → findBranch "First" brs ≡ just ("First" , ar , b)
        → tm-case (tm-bounded_lit 0) m brs ⇝ substArgs (tm-nat_lit 0 ∷ []) b

      ι-bounded-suc : ∀ {m brs ar b k}
        → findBranch "Next" brs ≡ just ("Next" , ar , b)
        → tm-case (tm-bounded_lit (suc k)) m brs ⇝ substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b


      -- δ: global f ⇝ body(f), only when the signature supplies a body.
      δ : ∀ {f body′} → Signature.body sig f ≡ just body′ → tm-global f ⇝ body′

      -- Congruence: application forces the function position.
      ξ-app₁ : ∀ {f f′ a} → f ⇝ f′ → tm-app f a ⇝ tm-app f′ a

      -- Congruence: application forces the argument once the function is a value.
      ξ-app₂ : ∀ {f a a′} → a ⇝ a′ → tm-app f a ⇝ tm-app f a′

      -- Congruence: case forces the scrutinee.
      ξ-case : ∀ {s s′ m brs} → s ⇝ s′ → tm-case s m brs ⇝ tm-case s′ m brs

      -- Congruence: case motive.
      ξ-case-motive : ∀ {s m m′ brs} → m ⇝ m′ → tm-case s m brs ⇝ tm-case s m′ brs

      -- Congruence: inert effect nodes reduce their subterms structurally.
      ξ-effect_type : ∀ {t t′} → t ⇝ t′ → tm-effect_type t ⇝ tm-effect_type t′
      ξ-effect_pure : ∀ {t t′} → t ⇝ t′ → tm-effect_pure t ⇝ tm-effect_pure t′
      ξ-effect_bind₁ : ∀ {e e′ k} → e ⇝ e′ → tm-effect_bind e k ⇝ tm-effect_bind e′ k
      ξ-effect_bind₂ : ∀ {e k k′} → k ⇝ k′ → tm-effect_bind e k ⇝ tm-effect_bind e k′

      -- Congruence: let forces its value.
      ξ-let : ∀ {g ty v v′ b} → v ⇝ v′ → tm-let g ty v b ⇝ tm-let g ty v′ b

      -- Congruence: let forces its declared type and its body.
      --
      -- A `let` body is normally reached only AFTER ζ fires, but a CONTEXT
      -- may reduce it directly (the body is a subterm). These rules make the
      -- relation able to reduce every subterm of a `let`, which the
      -- confluence development's parallel reduction needs.
      ξ-let-ty : ∀ {g ty ty′ v b} → ty ⇝ ty′ → tm-let g ty v b ⇝ tm-let g ty′ v b
      ξ-let-body : ∀ {g ty v b b′} → b ⇝ b′ → tm-let g ty v b ⇝ tm-let g ty v b′

      -- Congruence: constructors force their arguments. The rule is
      -- ELEMENT-INDEXED by a `Fin`: it reduces the argument at position `i`,
      -- leaving every other argument alone. This is what the confluence
      -- development's parallel reduction needs (it must simulate a parallel
      -- step by reducing one argument at a time), and it is unambiguous
      -- because the position is part of the rule.
      ξ-ctor-at : ∀ {n} {args : List Term} (i : Fin (len args)) {x′}
                → lookupAt args i ⇝ x′
                → tm-ctor n args ⇝ tm-ctor n (setAt args i x′)

      -- Congruence: data spines force their arguments, element-indexed. The
      -- params and indices carry separate positions, so the two rules are
      -- distinguishable by their `Fin` index.
      ξ-data-params-at : ∀ {n is} {ps : List Term} (i : Fin (len ps)) {x′}
                       → lookupAt ps i ⇝ x′
                       → tm-data n ps is ⇝ tm-data n (setAt ps i x′) is
      ξ-data-indices-at : ∀ {n ps} {is : List Term} (i : Fin (len is)) {x′}
                        → lookupAt is i ⇝ x′
                        → tm-data n ps is ⇝ tm-data n ps (setAt is i x′)

      -- Congruence: Π/λ force their domain (the codomain/body are under a binder).
      ξ-pi-dom : ∀ {g d d′ b} → d ⇝ d′ → tm-pi g d b ⇝ tm-pi g d′ b
      ξ-lam-dom : ∀ {g d d′ b} → d ⇝ d′ → tm-lam g d b ⇝ tm-lam g d′ b

      -- Congruence: Π/λ bodies reduce under the binder.
      ξ-pi-cod : ∀ {g d b b′} → b ⇝ b′ → tm-pi g d b ⇝ tm-pi g d b′
      ξ-lam-body : ∀ {g d b b′} → b ⇝ b′ → tm-lam g d b ⇝ tm-lam g d b′

    data _⇝*ᵗ_ : List Term → List Term → Set where
      ⇝*-nil  : [] ⇝*ᵗ []
      ⇝*-cons : ∀ {x x′ xs xs′} → x ⇝ x′ → xs ⇝*ᵗ xs′ → (x ∷ xs) ⇝*ᵗ (x′ ∷ xs′)

  ------------------------------------------------------------------------
  -- Multi-step reduction: the reflexive-transitive closure.
  ------------------------------------------------------------------------

  infix 4 _⇝*_

  data _⇝*_ : Term → Term → Set where
    ⇝*-refl  : ∀ {t} → t ⇝* t
    ⇝*-step  : ∀ {t u v} → t ⇝ u → u ⇝* v → t ⇝* v
