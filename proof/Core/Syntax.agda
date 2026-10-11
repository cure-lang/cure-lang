------------------------------------------------------------------------
-- Core syntax: the object language of the trusted kernel.
--
-- Faithful to `Cure.Core.Term` (lib/cure/core/term.ex) and the node
-- taxonomy in docs/KERNEL.md "Core Terms" / docs/SOUNDNESS.md §1.1:
--
--   * a fixed predicative universe hierarchy Type 0 : Type 1 : Type 2;
--   * graded dependent functions {:pi,g,dom,cod} / {:lam,g,dom,body} /
--     {:app,f,a} with g in the four-element QTT carrier;
--   * graded let {:let,g,ty,val,body}, ζ-transparent;
--   * indexed inductive families {:data,name,params,indices} with
--     constructors {:ctor,name,args};
--   * a dependent eliminator {:case,scrut,motive,branches};
--   * global references {:global,name};
--   * primitive numeric/atom/binary base types and their literals;
--   * inert effect terms {:effect_type,t} / {:effect_pure,a} /
--     {:effect_bind,e,k} — zero reduction rules;
--   * two development-only leaves: {:hole,name} and {:absurd}.
--
-- Variables are de Bruijn INDICES. We keep the raw `ℕ` index (rather than
-- a well-scoped Fin) so the syntax is a literal image of the Elixir
-- `{:var, k}` node; well-scopedness is a separate predicate (`Scoped`)
-- that the typing judgment carries, mirroring how the kernel's `Context`
-- is threaded alongside terms.
--
-- `Bool` and `Nat` are NOT primitive here either: they are ordinary
-- inductive families seeded into the signature (Cure.Core.Builtins.seed).
-- So there is no `bool`/`nat` node — only the generic tm-data`/tm-ctor`.
------------------------------------------------------------------------
module Core.Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.String using (String)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Core.Grade using (Grade; erased; linear; affine; unrestricted)
open import Core.Universe using (Level; l0; l1; l2)

------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------

-- Global/family/constructor names. Modelled as strings; the kernel uses
-- atoms, but nothing in the metatheory depends on the representation
-- beyond decidable equality, which we postulate for the signature layer.
Name : Set
Name = String

------------------------------------------------------------------------
-- A minimal integer carrier for the tm-int_lit` node. The kernel uses
-- arbitrary-precision integers; the metatheory treats them opaquely
-- (they are canonical values with no reduction rules of their own).
------------------------------------------------------------------------

data ℤ′ : Set where
  pos : ℕ → ℤ′
  negsuc : ℕ → ℤ′

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

-- A `:case` branch: constructor name, its arity, and the branch body.
-- The body lives under `arity` fresh binders (the constructor's fields).
-- The Core term type is mutually recursive with `Branch` via the case node.
data Term : Set
Branch : Set
Branch = Name × ℕ × Term

data Term where
  tm-type   : Level → Term
  tm-var    : ℕ → Term
  tm-pi     : Grade → Term → Term → Term
  tm-lam    : Grade → Term → Term → Term
  tm-let    : Grade → Term → Term → Term → Term
  tm-app    : Term → Term → Term
  tm-data   : Name → List Term → List Term → Term
  tm-ctor   : Name → List Term → Term
  tm-case   : Term → Term → List Branch → Term
  tm-global : Name → Term
  tm-int_type    : Term
  tm-int_lit     : ℤ′ → Term
  tm-nat_lit     : ℕ → Term
  tm-bounded_lit : ℕ → Term
  tm-float_type  : Term
  tm-float_lit   : Term
  tm-binary_type : Term
  tm-atom_type   : Term
  tm-atom_lit    : Name → Term
  tm-effect_type : Term → Term
  tm-effect_pure : Term → Term
  tm-effect_bind : Term → Term → Term
  tm-hole        : Name → Term
  tm-absurd      : Term

------------------------------------------------------------------------
-- Well-scopedness
--
-- `Scoped d t` says every free variable of `t` has index `< d`. This is the
-- predicate the typing judgment carries, mirroring the kernel's `Context`
-- depth discipline. `Closed t = Scoped 0 t`.
------------------------------------------------------------------------

mutual
  data ScopedBranches (d : ℕ) : List Branch → Set where
    sb[] : ScopedBranches d []
    sb∷  : ∀ {x xs} → ScopedBranch d x → ScopedBranches d xs → ScopedBranches d (x ∷ xs)

  data ScopedBranch (d : ℕ) : Branch → Set where
    sbranch : ∀ {cn ar b} → Scoped (d + ar) b → ScopedBranch d (cn , ar , b)

  data ScopedTerms (d : ℕ) : List Term → Set where
    st[] : ScopedTerms d []
    st∷  : ∀ {x xs} → Scoped d x → ScopedTerms d xs → ScopedTerms d (x ∷ xs)

  data Scoped (d : ℕ) : Term → Set where
    sc-type   : ∀ {l} → Scoped d (tm-type l)
    sc-var    : ∀ {k} → k < d → Scoped d (tm-var k)
    sc-pi     : ∀ {g a b} → Scoped d a → Scoped (suc d) b → Scoped d (tm-pi g a b)
    sc-lam    : ∀ {g a b} → Scoped d a → Scoped (suc d) b → Scoped d (tm-lam g a b)
    sc-let    : ∀ {g ty v b} → Scoped d ty → Scoped d v → Scoped (suc d) b → Scoped d (tm-let g ty v b)
    sc-app    : ∀ {f x} → Scoped d f → Scoped d x → Scoped d (tm-app f x)
    sc-data   : ∀ {n ps is} → ScopedTerms d ps → ScopedTerms d is → Scoped d (tm-data n ps is)
    sc-ctor   : ∀ {n args} → ScopedTerms d args → Scoped d (tm-ctor n args)
    sc-case   : ∀ {s m brs} → Scoped d s → Scoped d m → ScopedBranches d brs → Scoped d (tm-case s m brs)
    sc-global : ∀ {n} → Scoped d (tm-global n)
    sc-int_type    : Scoped d (tm-int_type)
    sc-int_lit     : ∀ {k} → Scoped d (tm-int_lit k)
    sc-nat_lit     : ∀ {k} → Scoped d (tm-nat_lit k)
    sc-bounded_lit : ∀ {k} → Scoped d (tm-bounded_lit k)
    sc-float_type  : Scoped d (tm-float_type)
    sc-float_lit   : Scoped d (tm-float_lit)
    sc-binary_type : Scoped d (tm-binary_type)
    sc-atom_type   : Scoped d (tm-atom_type)
    sc-atom_lit    : ∀ {n} → Scoped d (tm-atom_lit n)
    sc-effect_type : ∀ {t} → Scoped d t → Scoped d (tm-effect_type t)
    sc-effect_pure : ∀ {t} → Scoped d t → Scoped d (tm-effect_pure t)
    sc-effect_bind : ∀ {e k} → Scoped d e → Scoped d k → Scoped d (tm-effect_bind e k)
    sc-hole        : ∀ {n} → Scoped d (tm-hole n)
    sc-absurd      : Scoped d (tm-absurd)

Closed : Term → Set
Closed t = Scoped 0 t

ClosedBranch : Branch → Set
ClosedBranch b = ScopedBranch 0 b

------------------------------------------------------------------------
-- Renaming.
--
-- `rename ρ t` applies the index map `ρ` to every free variable of `t`.
-- Under a binder, `ρ` is extended by `ext ρ` (the new binder maps to
-- itself, older variables shift).
--
-- Renaming is the standard vehicle for weakening: a weakening is a
-- renaming that maps every index into a larger context. Using renaming
-- (rather than a raw `shift`) makes the context-extension naturality
-- automatic, which is exactly the binder-order issue raw shifting runs
-- into.
------------------------------------------------------------------------

Ren : Set
Ren = ℕ → ℕ

-- Extend a renaming under one binder.
ext : Ren → Ren
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

-- `ext` iterated `n` times.
ext^ : ℕ → Ren → Ren
ext^ zero ρ = ρ
ext^ (suc n) ρ = ext (ext^ n ρ)

mutual
  renameBranch : Ren → Branch → Branch
  renameBranch ρ (cn , ar , b) = cn , ar , rename (λ k → ext^ ar ρ k) b

  renameBranches : Ren → List Branch → List Branch
  renameBranches ρ [] = []
  renameBranches ρ (x ∷ xs) = renameBranch ρ x ∷ renameBranches ρ xs

  renameTerms : Ren → List Term → List Term
  renameTerms ρ [] = []
  renameTerms ρ (x ∷ xs) = rename ρ x ∷ renameTerms ρ xs

  rename : Ren → Term → Term
  rename ρ (tm-type l) = tm-type l
  rename ρ (tm-var k) = tm-var (ρ k)
  rename ρ (tm-pi g d c) = tm-pi g (rename ρ d) (rename (ext ρ) c)
  rename ρ (tm-lam g d b) = tm-lam g (rename ρ d) (rename (ext ρ) b)
  rename ρ (tm-let g ty v b) = tm-let g (rename ρ ty) (rename ρ v) (rename (ext ρ) b)
  rename ρ (tm-app f a) = tm-app (rename ρ f) (rename ρ a)
  rename ρ (tm-data n ps is) = tm-data n (renameTerms ρ ps) (renameTerms ρ is)
  rename ρ (tm-ctor n args) = tm-ctor n (renameTerms ρ args)
  rename ρ (tm-case s m brs) = tm-case (rename ρ s) (rename ρ m) (renameBranches ρ brs)
  rename ρ (tm-global n) = tm-global n
  rename ρ (tm-int_type) = tm-int_type
  rename ρ (tm-int_lit k) = tm-int_lit k
  rename ρ (tm-nat_lit k) = tm-nat_lit k
  rename ρ (tm-bounded_lit k) = tm-bounded_lit k
  rename ρ (tm-float_type) = tm-float_type
  rename ρ (tm-float_lit) = tm-float_lit
  rename ρ (tm-binary_type) = tm-binary_type
  rename ρ (tm-atom_type) = tm-atom_type
  rename ρ (tm-atom_lit n) = tm-atom_lit n
  rename ρ (tm-effect_type t) = tm-effect_type (rename ρ t)
  rename ρ (tm-effect_pure t) = tm-effect_pure (rename ρ t)
  rename ρ (tm-effect_bind e k) = tm-effect_bind (rename ρ e) (rename ρ k)
  rename ρ (tm-hole n) = tm-hole n
  rename ρ (tm-absurd) = tm-absurd


------------------------------------------------------------------------
-- Simultaneous substitution.
--
-- A simultaneous substitution maps every source index to a term. Applying
-- it replaces every free variable at once, which is what the substitution
-- lemma needs: substituting index 0 with `a` AND renumbering the indices
-- above it down by one is the single substitution
--
--     σ zero     = a
--     σ (suc k)  = tm-var k
--
-- Under a binder the substitution is extended: the new binder maps to
-- itself, and every other index is shifted by one to make room.
------------------------------------------------------------------------

Sub : Set
Sub = ℕ → Term

-- Extend a substitution under one binder.
-- The weakening renaming: shift every index up by one.
wk : Ren
wk k = suc k

extSub : Sub → Sub
extSub σ zero = tm-var zero
extSub σ (suc k) = rename wk (σ k)


-- `extSub` iterated `n` times.
extSub^ : ℕ → Sub → Sub
extSub^ zero σ = σ
extSub^ (suc n) σ = extSub (extSub^ n σ)

-- The "top" substitution: replace index 0 with `a` and renumber the indices
-- above it down by one. This is the substitution the β and ζ rules use.
topSub : Term → Sub
topSub a zero = a
topSub a (suc k) = tm-var k

mutual
  substTermsS : Sub → List Term → List Term
  substTermsS σ [] = []
  substTermsS σ (x ∷ xs) = substS σ x ∷ substTermsS σ xs

  substBranchesS : Sub → List Branch → List Branch
  substBranchesS σ [] = []
  substBranchesS σ (x ∷ xs) = substBranchS σ x ∷ substBranchesS σ xs

  substBranchS : Sub → Branch → Branch
  substBranchS σ (cn , ar , b) = cn , ar , substS (extSub^ ar σ) b

  substS : Sub → Term → Term
  substS σ (tm-type l) = tm-type l
  substS σ (tm-var k) = σ k
  substS σ (tm-pi g d c) = tm-pi g (substS σ d) (substS (extSub σ) c)
  substS σ (tm-lam g d b) = tm-lam g (substS σ d) (substS (extSub σ) b)
  substS σ (tm-let g ty v b) = tm-let g (substS σ ty) (substS σ v) (substS (extSub σ) b)
  substS σ (tm-app f a) = tm-app (substS σ f) (substS σ a)
  substS σ (tm-data n ps is) = tm-data n (substTermsS σ ps) (substTermsS σ is)
  substS σ (tm-ctor n args) = tm-ctor n (substTermsS σ args)
  substS σ (tm-case s m brs) = tm-case (substS σ s) (substS σ m) (substBranchesS σ brs)
  substS σ (tm-global n) = tm-global n
  substS σ (tm-int_type) = tm-int_type
  substS σ (tm-int_lit k) = tm-int_lit k
  substS σ (tm-nat_lit k) = tm-nat_lit k
  substS σ (tm-bounded_lit k) = tm-bounded_lit k
  substS σ (tm-float_type) = tm-float_type
  substS σ (tm-float_lit) = tm-float_lit
  substS σ (tm-binary_type) = tm-binary_type
  substS σ (tm-atom_type) = tm-atom_type
  substS σ (tm-atom_lit n) = tm-atom_lit n
  substS σ (tm-effect_type t) = tm-effect_type (substS σ t)
  substS σ (tm-effect_pure t) = tm-effect_pure (substS σ t)
  substS σ (tm-effect_bind e k) = tm-effect_bind (substS σ e) (substS σ k)
  substS σ (tm-hole n) = tm-hole n
  substS σ (tm-absurd) = tm-absurd

------------------------------------------------------------------------
-- Substituting a value at the top of a type.
--
-- This is the `let` rule's result type (`substTopT v T`), and the
-- codomain instantiation of `⇒-app` (`substTopT a c`). It lives here, in
-- the syntactic layer, so the purely-syntactic renaming/substitution laws
-- can speak about it without importing the typing judgment.
------------------------------------------------------------------------

substTopT : Term → Term → Term
substTopT v T = substS (topSub v) T

------------------------------------------------------------------------
-- de Bruijn shift (lift every free variable ≥ cutoff by amount)
--
-- Mirrors `Term.shift/3` exactly, including the `:case` branch rule
-- `shift(b, a, c + ar)` and the effect nodes' same-cutoff recursion.
------------------------------------------------------------------------

-- The shift renaming, defined by recursion on the CUTOFF so that its
-- extension under a binder is DEFINITIONAL: `ext (shiftRen a c) ≡ shiftRen a (suc c)`.
-- This is what makes `shift` commute with `rename` (and hence with `substS`).
shiftRen : ℕ → ℕ → Ren
shiftRen a zero k = k + a
shiftRen a (suc c) zero = zero
shiftRen a (suc c) (suc k) = suc (shiftRen a c k)

-- `ext (shiftRen a c) ≡ shiftRen a (suc c)`, definitionally.
ext-shiftRen : ∀ a c k → ext (shiftRen a c) k ≡ shiftRen a (suc c) k
ext-shiftRen a c zero = refl
ext-shiftRen a c (suc k) = refl

-- `shift a c t = rename (shiftRen a c) t`: shifting is a renaming, so it
-- inherits the renaming laws (composition, commutation with substitution).
shift : ℕ → ℕ → Term → Term
shift a c t = rename (shiftRen a c) t

-- Shifting a branch body at the branch's arity.
shiftBranch : ℕ → ℕ → Branch → Branch
shiftBranch a c (cn , ar , b) = cn , ar , shift a (c + ar) b

------------------------------------------------------------------------
-- Renaming composes.
--
-- `rename ρ (rename σ t) ≡ rename (ρ ∘ σ) t`: two renamings compose.
-- The binder case uses `ext ρ ∘ ext σ ≡ ext (ρ ∘ σ)`, which holds
-- definitionally.
------------------------------------------------------------------------
open import Function using (_∘_)

cong₃ : ∀ {A B C D : Set} {a a′ : A} {b b′ : B} {c c′ : C}
     → (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

postulate funext-ren : ∀ {ρ σ : Ren} → (∀ k → ρ k ≡ σ k) → ρ ≡ σ

mutual
  rename-compose-terms : ∀ ρ σ ts → renameTerms ρ (renameTerms σ ts) ≡ renameTerms (ρ ∘ σ) ts
  rename-compose-terms ρ σ [] = refl
  rename-compose-terms ρ σ (x ∷ xs) =
    cong₂ _∷_ (rename-compose ρ σ x) (rename-compose-terms ρ σ xs)

  rename-compose-branches : ∀ ρ σ bs → renameBranches ρ (renameBranches σ bs) ≡ renameBranches (ρ ∘ σ) bs
  rename-compose-branches ρ σ [] = refl
  rename-compose-branches ρ σ (x ∷ xs) =
    cong₂ _∷_ (rename-compose-branch ρ σ x) (rename-compose-branches ρ σ xs)

  rename-compose-branch : ∀ ρ σ b → renameBranch ρ (renameBranch σ b) ≡ renameBranch (ρ ∘ σ) b
  rename-compose-branch ρ σ (cn , ar , b) =
    cong (λ x → cn , ar , x)
         (trans (rename-compose (ext^ ar ρ) (ext^ ar σ) b)
                (cong (λ x → rename x b) (funext-ren (λ k → sym (ext^-compose ar ρ σ k)))))
    where
      ext^-compose : ∀ n ρ σ k → ext^ n (ρ ∘ σ) k ≡ ext^ n ρ (ext^ n σ k)
      ext^-compose zero ρ σ k = refl
      ext^-compose (suc n) ρ σ zero = refl
      ext^-compose (suc n) ρ σ (suc k) = cong suc (ext^-compose n ρ σ k)

  ext-compose : ∀ ρ σ k → (ext ρ ∘ ext σ) k ≡ ext (ρ ∘ σ) k
  ext-compose ρ σ zero = refl
  ext-compose ρ σ (suc k) = refl

  rename-compose : ∀ ρ σ t → rename ρ (rename σ t) ≡ rename (ρ ∘ σ) t
  rename-compose ρ σ (tm-type l) = refl
  rename-compose ρ σ (tm-var k) = refl
  rename-compose ρ σ (tm-pi g d c) =
    cong₂ (tm-pi g) (rename-compose ρ σ d)
          (trans (rename-compose (ext ρ) (ext σ) c)
                 (cong (λ x → rename x c) (funext-ren (ext-compose ρ σ))))
  rename-compose ρ σ (tm-lam g d b) =
    cong₂ (tm-lam g) (rename-compose ρ σ d)
          (trans (rename-compose (ext ρ) (ext σ) b)
                 (cong (λ x → rename x b) (funext-ren (ext-compose ρ σ))))
  rename-compose ρ σ (tm-let g ty v b) =
    cong₃ (tm-let g) (rename-compose ρ σ ty) (rename-compose ρ σ v)
          (trans (rename-compose (ext ρ) (ext σ) b)
                 (cong (λ x → rename x b) (funext-ren (ext-compose ρ σ))))
  rename-compose ρ σ (tm-app f a) = cong₂ tm-app (rename-compose ρ σ f) (rename-compose ρ σ a)
  rename-compose ρ σ (tm-data n ps is) = cong₂ (tm-data n) (rename-compose-terms ρ σ ps) (rename-compose-terms ρ σ is)
  rename-compose ρ σ (tm-ctor n args) = cong (tm-ctor n) (rename-compose-terms ρ σ args)
  rename-compose ρ σ (tm-case s m brs) =
    cong₃ tm-case (rename-compose ρ σ s) (rename-compose ρ σ m) (rename-compose-branches ρ σ brs)
  rename-compose ρ σ (tm-global n) = refl
  rename-compose ρ σ (tm-int_type) = refl
  rename-compose ρ σ (tm-int_lit k) = refl
  rename-compose ρ σ (tm-nat_lit k) = refl
  rename-compose ρ σ (tm-bounded_lit k) = refl
  rename-compose ρ σ (tm-float_type) = refl
  rename-compose ρ σ (tm-float_lit) = refl
  rename-compose ρ σ (tm-binary_type) = refl
  rename-compose ρ σ (tm-atom_type) = refl
  rename-compose ρ σ (tm-atom_lit n) = refl
  rename-compose ρ σ (tm-effect_type t) = cong tm-effect_type (rename-compose ρ σ t)
  rename-compose ρ σ (tm-effect_pure t) = cong tm-effect_pure (rename-compose ρ σ t)
  rename-compose ρ σ (tm-effect_bind e k) = cong₂ tm-effect_bind (rename-compose ρ σ e) (rename-compose ρ σ k)
  rename-compose ρ σ (tm-hole n) = refl
  rename-compose ρ σ (tm-absurd) = refl

------------------------------------------------------------------------
-- `ext ρ ∘ wk ≡ wk ∘ ρ`.
------------------------------------------------------------------------

ext-wk-compose : ∀ ρ k → (ext ρ ∘ wk) k ≡ (wk ∘ ρ) k
ext-wk-compose ρ k = refl


------------------------------------------------------------------------
-- `rename wk (rename ρ t) ≡ rename (ext ρ) (rename wk t)`.
--
-- The two ways of shifting a renamed term agree, because
-- `wk ∘ ρ ≡ ext ρ ∘ wk` (both map `k ↦ suc (ρ k)`).
------------------------------------------------------------------------

ext-wk-rename : ∀ ρ t → rename wk (rename ρ t) ≡ rename (ext ρ) (rename wk t)
ext-wk-rename ρ t =
  trans (rename-compose wk ρ t)
        (trans (cong (λ x → rename x t) (funext-ren (ext-wk-compose ρ)))
               (sym (rename-compose (ext ρ) wk t)))

------------------------------------------------------------------------
-- `renameTerms ρ ts ≡ map (rename ρ) ts`.
------------------------------------------------------------------------

renameTerms-map : ∀ ρ ts → renameTerms ρ ts ≡ map (rename ρ) ts
renameTerms-map ρ [] = refl
renameTerms-map ρ (x ∷ xs) = cong₂ _∷_ refl (renameTerms-map ρ xs)

-- `substTermsS σ ts ≡ map (substS σ) ts`.
substTerms-map : ∀ σ ts → substTermsS σ ts ≡ map (substS σ) ts
substTerms-map σ [] = refl
substTerms-map σ (x ∷ xs) = cong₂ _∷_ refl (substTerms-map σ xs)

------------------------------------------------------------------------
-- Shift composition.
------------------------------------------------------------------------

-- `shift a (c + ar) (shift ar 0 r) ≡ shift ar 0 (shift a c r)`.
shiftRen-compose : ∀ a c ar k → shiftRen a (c + ar) (shiftRen ar 0 k) ≡ shiftRen ar 0 (shiftRen a c k)
shiftRen-compose a c zero k =
  trans (cong (λ x → shiftRen a x (k + 0)) (+-identityʳ c))
        (trans (cong (shiftRen a c) (+-identityʳ k))
               (sym (+-identityʳ (shiftRen a c k))))
shiftRen-compose a c (suc ar) k =
  trans (cong (λ x → shiftRen a x (k + suc ar)) (+-suc c ar))
        (trans (cong (λ x → shiftRen a (suc (c + ar)) x) (+-suc k ar))
               (trans (cong suc (shiftRen-compose a c ar k))
                      (sym (+-suc (shiftRen a c k) ar))))

shift-compose : ∀ a c ar r → shift a (c + ar) (shift ar 0 r) ≡ shift ar 0 (shift a c r)
shift-compose a c ar r =
  trans (rename-compose (shiftRen a (c + ar)) (shiftRen ar 0) r)
        (trans (cong (λ ρ → rename ρ r) (funext-ren (shiftRen-compose a c ar)))
               (sym (rename-compose (shiftRen ar 0) (shiftRen a c) r)))



------------------------------------------------------------------------
-- Canonical forms, neutrals, and values.
--
-- The kernel's notion of a value (`MetaCheck.canonical_head?/1`) includes
-- both introduction forms (λ, ctor, Π, Type, data, literals, effect
-- formers) and NEUTRALS (stuck computations):
--
--   * `Canonical` — the introduction forms, which cannot be stuck;
--   * `Neutral`   — a variable, global, hole, or eliminator stuck on a
--                   neutral;
--   * `Value`     — their union, recovering the kernel's notion.
--
-- These live here (rather than in Proof/Values.agda) because the reduction
-- relation needs `Value` to state its β/ζ rules: the kernel's β fires only
-- on `apply(vlam, varg)` — the argument is a VALUE. Requiring the argument
-- to be a value is what makes Preservation's β/ζ cases go through, since a
-- value of a given type INFERS that type (`value-infer` below).
--
-- The `Canonical`/`Neutral` split still matters for the canonical-form
-- lemmas (Proof/CanonicalForms.agda): "every value of Π type is a λ" is
-- FALSE for neutrals (a stuck application of Π type is a value).
------------------------------------------------------------------------

data Canonical : Term → Set where
  c-type    : ∀ {l} → Canonical (tm-type l)
  c-pi      : ∀ {g d c} → Canonical (tm-pi g d c)
  c-lam     : ∀ {g d b} → Canonical (tm-lam g d b)
  c-data    : ∀ {n ps is} → Canonical (tm-data n ps is)
  c-ctor    : ∀ {n args} → Canonical (tm-ctor n args)
  c-int_type    : Canonical tm-int_type
  c-int_lit     : ∀ {k} → Canonical (tm-int_lit k)
  c-nat_lit     : ∀ {k} → Canonical (tm-nat_lit k)
  c-bounded_lit : ∀ {k} → Canonical (tm-bounded_lit k)
  c-float_type  : Canonical tm-float_type
  c-float_lit   : Canonical tm-float_lit
  c-binary_type : Canonical tm-binary_type
  c-atom_type   : Canonical tm-atom_type
  c-atom_lit    : ∀ {n} → Canonical (tm-atom_lit n)
  c-effect_type : ∀ {t} → Canonical (tm-effect_type t)
  c-effect_pure : ∀ {t} → Canonical (tm-effect_pure t)
  c-effect_bind : ∀ {e k} → Canonical (tm-effect_bind e k)

data Neutral : Term → Set where
  n-var    : ∀ {k} → Neutral (tm-var k)
  n-global : ∀ {n} → Neutral (tm-global n)
  n-hole   : ∀ {n} → Neutral (tm-hole n)
  n-app    : ∀ {f a} → Neutral f → Neutral (tm-app f a)
  n-case   : ∀ {s m brs} → Neutral s → Neutral (tm-case s m brs)

data Value : Term → Set where
  canonical : ∀ {t} → Canonical t → Value t
  neutral   : ∀ {t} → Neutral t → Value t
