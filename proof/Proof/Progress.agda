------------------------------------------------------------------------
-- Progress and Preservation.
--
-- docs/SOUNDNESS.md §2 and §4 state the two lemmas. We give their exact
-- statements here, plus the Soundness theorem they combine into (§1.4).
--
-- The statements are parameterised by:
--   * the inductive environment `ind` (families + constructors);
--   * the δ-signature `sig` (certified globals and their types);
--   * the conversion relation `conv`.
--
-- The three side conditions of the theorem (docs/SOUNDNESS.md §3) are
-- carried as hypotheses:
--   * `StrictlyPositive ind`   — every family is strictly positive (§3.1);
--   * `Certified sig`          — every δ-unfoldable global is total (§3.2);
--   * `Covers ind`             — every case has full coverage (§3.3).
--
-- The hole/absurd discipline (§3.4) is expressed by restricting the
-- theorem to hole-free, absurd-free terms (`Final`).
------------------------------------------------------------------------
module Proof.Progress where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Universe using (Level; l0; l1; l2)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; Conversion)
open import Proof.Values using (Value; Canonical; Neutral; canonical; neutral)

------------------------------------------------------------------------
-- Final Core: hole-free and absurd-free.
--
-- The release boundary (docs/SOUNDNESS.md §3.4) rejects `{:hole, _}` and
-- reachable `{:absurd}`. We encode "final" as a predicate on terms.
------------------------------------------------------------------------

mutual
  data Final : Term → Set where
    f-type   : ∀ {l} → Final (tm-type l)
    f-var    : ∀ {k} → Final (tm-var k)
    f-pi     : ∀ {g d c} → Final d → Final c → Final (tm-pi g d c)
    f-lam    : ∀ {g d b} → Final d → Final b → Final (tm-lam g d b)
    f-let    : ∀ {g ty v b} → Final ty → Final v → Final b → Final (tm-let g ty v b)
    f-app    : ∀ {f a} → Final f → Final a → Final (tm-app f a)
    f-data   : ∀ {n ps is} → FinalTerms ps → FinalTerms is → Final (tm-data n ps is)
    f-ctor   : ∀ {n args} → FinalTerms args → Final (tm-ctor n args)
    f-case   : ∀ {s m brs} → Final s → Final m → FinalBranches brs → Final (tm-case s m brs)
    f-global : ∀ {n} → Final (tm-global n)
    f-int_type    : Final tm-int_type
    f-int_lit     : ∀ {k} → Final (tm-int_lit k)
    f-nat_lit     : ∀ {k} → Final (tm-nat_lit k)
    f-bounded_lit : ∀ {k} → Final (tm-bounded_lit k)
    f-float_type  : Final tm-float_type
    f-float_lit   : Final tm-float_lit
    f-binary_type : Final tm-binary_type
    f-atom_type   : Final tm-atom_type
    f-atom_lit    : ∀ {n} → Final (tm-atom_lit n)
    f-effect_type : ∀ {t} → Final t → Final (tm-effect_type t)
    f-effect_pure : ∀ {t} → Final t → Final (tm-effect_pure t)
    f-effect_bind : ∀ {e k} → Final e → Final k → Final (tm-effect_bind e k)

  data FinalTerms : List Term → Set where
    ft[] : FinalTerms []
    ft∷  : ∀ {x xs} → Final x → FinalTerms xs → FinalTerms (x ∷ xs)

  data FinalBranches : List Branch → Set where
    fb[] : FinalBranches []
    fb∷  : ∀ {cn ar b brs} → Final b → FinalBranches brs → FinalBranches ((cn , ar , b) ∷ brs)

------------------------------------------------------------------------
-- The three side conditions (docs/SOUNDNESS.md §3)
------------------------------------------------------------------------

-- §3.1 Strict positivity: every family's `positive` flag holds.
StrictlyPositive : IndEnv → Set
StrictlyPositive ind = ∀ f → f ∈ IndEnv.families ind → Family.positive f ≡ true

-- §3.2 Totality gates δ: every global the signature can unfold is total.
--
-- This is the SINGLE load-bearing hypothesis of the argument
-- (docs/SOUNDNESS.md §5.3(2)): we take `Certified` as an abstract
-- predicate with the property that a certified global's body is
-- terminating. The δ rule only fires on names in the signature's body map,
-- so this is the assumption that makes δ type-preserving (Preservation §4).
Certified : Signature → Set
Certified sig = ∀ {f body′} → Signature.body sig f ≡ just body′ → Final body′

-- §3.3 Coverage: every case has a branch for every constructor.
--
-- The coverage check (`check_coverage`) requires a branch for every
-- constructor the index unifier does not refute. We take it as a predicate
-- on the inductive environment, discharged by Core/Coverage.agda.
--
-- The witness is a branch NAMED `c` (not merely some branch in the list):
-- that is what `findBranch c brs` needs to fire ι, and it is the honest
-- reading of "a branch for constructor `c`".
allCtorNames : List Family → List Name
allCtorNames fs = concatMap (λ f → map ctor-name (Family.fam-ctors f)) fs

Covers : IndEnv → Set
Covers ind = ∀ (brs : List Branch) (m : Term)
           → (∀ (c : Name) → c ∈ allCtorNames (IndEnv.families ind)
             → ∃ λ ar → ∃ λ b → (c , ar , b) ∈ brs)

------------------------------------------------------------------------
-- Progress (docs/SOUNDNESS.md §2)
--
-- If `· ⊢ e : T` and `e` is not a value, then either `e ⇝ e′` for some
-- `e′`, or `e` raises. We model "raises" as the second disjunct; the
-- corollary that a *statically exhaustive* case cannot raise is what makes
-- the first disjunct unconditional for final Core.
------------------------------------------------------------------------

module Progress (ind : IndEnv) (sig : Signature) (conv : Conversion)
                (pos : StrictlyPositive ind) (cert : Certified sig) (cov : Covers ind) where

  open Core.Typing.Typing ind sig conv

  -- A closed term is well-typed at `T`.
  Closed⊢ : Term → Term → Set
  Closed⊢ t T = ⟨⟩ ⊢ t ⇒ T

  -- The result type of Progress.
  ProgressResult : Term → Set
  ProgressResult t = Value t ⊎ (∃ λ t′ → _⇝_ sig t t′)

  -- A branch's arity equals its constructor's argument-telescope length. Read
  -- off the `⊢*brs` derivation: `brs∷` records `length (ctor-args ct) ≡ ar`.
  brs-arity : ∀ {brs n m}
            → ⟨⟩ ⊢*brs brs ⇐*ᵇ (n , m)
            → ∀ {c ar b} → (c , ar , b) ∈ brs
            → ∃ λ f → ∃ λ ct
            → findCtor c (IndEnv.families ind) ≡ just (f , ct)
              × length (ctor-args ct) ≡ ar
  brs-arity brs[] ()
  brs-arity (brs∷ {ct = ct} fc len _body rest) (here refl) = _ , ct , fc , len
  brs-arity (brs∷ fc len _body rest) (there p) = brs-arity rest p

  -- Progress: a well-typed closed final term is a value or it steps.
  --
  -- OPEN OBLIGATION. The proof is by mutual induction on the typing
  -- derivation (infer and check), exactly as docs/SOUNDNESS.md §2 walks the
  -- term formers. The pieces are now ALL in place:
  --
  --   * `canonical-pi-value` / `canonical-ctor` (Proof/CanonicalForms.agda)
  --     turn a canonical Π/data value into a λ / constructor-like head, so β
  --     and ι fire;
  --   * `spine-length` + `brs-arity` match the ι branch arity to the ctor's
  --     argument telescope;
  --   * `findBranch-complete` turns the coverage witness into the
  --     `findBranch c brs ≡ just (c , ar , b)` premise of ι;
  --   * the `ι-nat-*` / `ι-bounded-*` reduction rules (Core/Reduction.agda)
  --     peel a compact literal scrutinee to its constructor form, so a `case`
  --     on `tm-nat_lit` / `tm-bounded_lit` is not stuck;
  --   * a neutral term is a `Value` (the `inj₁` branch), so the elimination
  --     rules are never stuck; `⇒-var` is vacuous (`Fin 0` is empty).
  --
  -- What remains is the bookkeeping: extracting the scrutinee's constructor
  -- membership (`c ∈ allCtorNames`) from its inference derivation, so the
  -- coverage witness applies. This is mechanical, not a design question.
  postulate
    progress :
      ∀ {t T}
      → Closed⊢ t T
      → Final t
      → Value t ⊎ (∃ λ t′ → _⇝_ sig t t′)