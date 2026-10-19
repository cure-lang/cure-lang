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
-- Signature-side obligations (docs/SOUNDNESS.md §3) are carried as hypotheses:
--   * `StrictlyPositive ind`   — every family is strictly positive (§3.1);
--   * `Certified sig`          — body FINALITY only, not termination;
-- Coverage (§3.3) is now local evidence carried by each ⇒-case derivation,
-- not a hypothesis about every possible raw branch list.
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
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Core.Grade using (Grade)
open import Core.Syntax
open import Core.Signature
open import Core.Coverage
open import Core.Reduction
open import Core.Typing using (Ctx; ⟨⟩; _▷_; lookup; extend; Conversion)
open import Proof.Values using (Value; Canonical; Neutral; canonical; neutral)
open import Proof.Inversion
open import Proof.CanonicalForms

------------------------------------------------------------------------
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

-- Body finality only: this predicate does NOT express termination.
-- Certified is retained as a compatibility name for legacy consumers.
-- Case coverage is provided by Core.Coverage and the ⇒-case typing rule.
BodiesFinal : Signature → Set
BodiesFinal sig = ∀ {f body′} → Signature.body sig f ≡ just body′ → Final body′
Certified : Signature → Set
Certified = BodiesFinal

-- Constructor names used by the builtin signature invariant. Actual case
-- coverage comes from CaseCoverage, not from this environment-wide list.
allCtorNames : List Family → List Name
allCtorNames fs = concatMap (λ f → map ctor-name (Family.fam-ctors f)) fs

-- The builtin families' constructors carry their canonical basenames
-- (`Z`/`S` for Nat, `First`/`Next` for Bounded). This is what lets Progress's
-- `case` on a compact `tm-nat_lit` / `tm-bounded_lit` scrutinee find the
-- branch the peeling reduction rules (`ι-nat-*` / `ι-bounded-*`) require. It
-- is a well-formedness side condition on the environment (the kernel's
-- `@builtin_ctor_aliases` map is the runtime counterpart).
BuiltinCtors : IndEnv → Set
BuiltinCtors ind =
    "Z" ∈ allCtorNames (IndEnv.families ind)
  × "S" ∈ allCtorNames (IndEnv.families ind)
  × "First" ∈ allCtorNames (IndEnv.families ind)
  × "Next" ∈ allCtorNames (IndEnv.families ind)
  -- The `nat` and `bounded` builtin families exist.
  × (∃ λ N → IndEnv.builtins ind "nat" ≡ just N)
  × (∃ λ B → IndEnv.builtins ind "bounded" ≡ just B)
  -- The builtin constructors' ARGUMENT TELESCOPES are the canonical ones:
  -- `Z` takes no fields; `S` takes the predecessor (a `Nat`); `First` takes
  -- the bound (a `Nat`); `Next` takes the bound and the predecessor. This is
  -- what lets the literal-peel ι rules (`ι-nat-*` / `ι-bounded-*`) relate the
  -- branch body's field variables to the peeled arguments.
  × (∀ {f} {ct} → findCtor "Z" (IndEnv.families ind) ≡ just (f , ct) → ctor-args ct ≡ [])
  × (∀ {f} {ct} {N} → IndEnv.builtins ind "nat" ≡ just N
      → findCtor "S" (IndEnv.families ind) ≡ just (f , ct)
      → ctor-args ct ≡ ("_" , tm-data N [] []) ∷ [])
  × (∀ {f} {ct} {N} → IndEnv.builtins ind "nat" ≡ just N
      → findCtor "First" (IndEnv.families ind) ≡ just (f , ct)
      → ctor-args ct ≡ ("_" , tm-data N [] []) ∷ [])
  × (∀ {f} {ct} {N} {B} → IndEnv.builtins ind "nat" ≡ just N
      → IndEnv.builtins ind "bounded" ≡ just B
      → findCtor "Next" (IndEnv.families ind) ≡ just (f , ct)
      → ctor-args ct ≡ ("_" , tm-data N [] []) ∷ ("_" , tm-data B [] []) ∷ [])

-- Progress (docs/SOUNDNESS.md §2)
--
-- If `· ⊢ e : T` and `e` is not a value, then either `e ⇝ e′` for some
-- `e′`, or `e` raises. We model "raises" as the second disjunct; the
-- corollary that a *statically exhaustive* case cannot raise is what makes
-- the first disjunct unconditional for final Core.
------------------------------------------------------------------------

module Progress (ind : IndEnv) (sig : Signature) (conv : Conversion)
                (pos : StrictlyPositive ind) (cert : Certified sig)
                (bc : BuiltinCtors ind) where

  open Core.Typing.Typing ind sig conv
  open Proof.Inversion.Invert ind sig conv
  open Proof.CanonicalForms.CF ind sig conv

  -- A closed term is well-typed at `T`.
  Closed⊢ : Term → Term → Set
  Closed⊢ t T = ⟨⟩ ⊢ t ⇒ T

  -- The result type of Progress.
  ProgressResult : Term → Set
  ProgressResult t = Value t ⊎ (∃ λ t′ → _⇝_ sig t t′)

  -- Constructor inference exposes the owning family and its checked
  -- spine, so local coverage applies only to that family.
  ctor-info : ∀ {c args n ps is}
    → ⟨⟩ ⊢ tm-ctor c args ⇒ tm-data n ps is
    → ∃ λ f → ∃ λ ct
    → findCtor c (IndEnv.families ind) ≡ just (f , ct)
      × fam-name f ≡ n × (⟨⟩ ⊢* args ⇐* ctor-args ct)
  ctor-info = constructor-data

  nat-lit-family : ∀ {k n ps is}
    → ⟨⟩ ⊢ tm-nat_lit k ⇒ tm-data n ps is
    → IndEnv.builtins ind "nat" ≡ just n
  nat-lit-family = nat-data-family

  bounded-lit-family : ∀ {k n ps is}
    → ⟨⟩ ⊢ tm-bounded_lit k ⇒ tm-data n ps is
    → IndEnv.builtins ind "bounded" ≡ just n
  bounded-lit-family = bounded-data-family

  case-ctor-step : ∀ {c args n ps is m brs}
    → ⟨⟩ ⊢ tm-ctor c args ⇒ tm-data n ps is
    → CaseCoverage ind n brs
    → ProgressResult (tm-case (tm-ctor c args) m brs)
  case-ctor-step {c} {args} p covered with ctor-info p
  ... | f , ct , fc , owner , sp with ctor-covered covered fc owner
  ... | b , found = inj₂ (substArgs args b , ι found (spine-length sp))

  case-nat-step : ∀ {n} (k : ℕ) (brs : List Branch) (m : Term)
    → IndEnv.builtins ind "nat" ≡ just n → CaseCoverage ind n brs
    → ProgressResult (tm-case (tm-nat_lit k) m brs)
  case-nat-step zero brs m builtin covered with nat-zero-covered covered builtin
  ... | b , found = inj₂ (substArgs [] b , ι-nat-zero found refl)
  case-nat-step (suc k) brs m builtin covered with nat-suc-covered covered builtin
  ... | b , found = inj₂ (substArgs (tm-nat_lit k ∷ []) b , ι-nat-suc found refl)

  case-bounded-step : ∀ {n} (k : ℕ) (brs : List Branch) (m : Term)
    → IndEnv.builtins ind "bounded" ≡ just n → CaseCoverage ind n brs
    → ProgressResult (tm-case (tm-bounded_lit k) m brs)
  case-bounded-step zero brs m builtin covered with bounded-zero-covered covered builtin
  ... | b , found = inj₂ (substArgs (tm-nat_lit 0 ∷ []) b , ι-bounded-zero found refl)
  case-bounded-step (suc k) brs m builtin covered with bounded-suc-covered covered builtin
  ... | b , found = inj₂ (substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b ,
                         ι-bounded-suc found refl)
  -- Progress: a well-typed closed final term is a value or it steps.
  --
  -- PROVED by mutual induction on the typing derivation (infer and check),
  -- exactly as docs/SOUNDNESS.md §2 walks the term formers. The canonical-form
  -- lemmas turn a canonical Π/data value into a λ / constructor-like head, so β
  -- and ι fire; a neutral term is a `Value` (the `inj₁` branch), so the
  -- elimination rules are never stuck; `⇒-var` is vacuous (`Fin 0` is empty).
  mutual
    progress⇒ :
      ∀ {t T}
      → ⟨⟩ ⊢ t ⇒ T
      → Final t
      → ProgressResult t

    progress⇐ :
      ∀ {t T}
      → ⟨⟩ ⊢ t ⇐ T
      → Final t
      → ProgressResult t

    -- `⇒-var` needs `Fin 0`, which is empty: a closed term has no free variable.
    progress⇒ (⇒-var ()) ff
    progress⇒ (⇒-type p) ff = inj₁ (canonical c-type)
    progress⇒ (⇒-pi p q) (f-pi fd fc) = inj₁ (canonical c-pi)
    progress⇒ (⇒-lam p q) (f-lam fd fb) = inj₁ (canonical c-lam)
    progress⇒ (⇒-int_type) ff = inj₁ (canonical c-int_type)
    progress⇒ (⇒-float_type) ff = inj₁ (canonical c-float_type)
    progress⇒ (⇒-binary_type) ff = inj₁ (canonical c-binary_type)
    progress⇒ (⇒-atom_type) ff = inj₁ (canonical c-atom_type)
    progress⇒ (⇒-int_lit) ff = inj₁ (canonical c-int_lit)
    progress⇒ (⇒-float_lit) ff = inj₁ (canonical c-float_lit)
    progress⇒ (⇒-atom_lit) ff = inj₁ (canonical c-atom_lit)
    progress⇒ (⇒-nat_lit p) ff = inj₁ (canonical c-nat_lit)
    progress⇒ (⇒-bounded_lit p) ff = inj₁ (canonical c-bounded_lit)
    progress⇒ (⇒-data p q r) (f-data fps fis) = inj₁ (canonical c-data)
    progress⇒ (⇒-ctor p q) (f-ctor fargs) = inj₁ (canonical c-ctor)
    progress⇒ (⇒-effect_type p) (f-effect_type ft) = inj₁ (canonical c-effect_type)
    progress⇒ (⇒-effect_pure p) (f-effect_pure ft) = inj₁ (canonical c-effect_pure)
    progress⇒ (⇒-effect_bind p q) (f-effect_bind fe fk) = inj₁ (canonical c-effect_bind)

    -- Application: reduce the function, then the argument, then β.
    progress⇒ (⇒-app {f = f} {a = a} p q) (f-app ff fa) with progress⇒ p ff
    ... | inj₂ (f′ , step) = inj₂ (tm-app f′ a , ξ-app₁ step)
    ... | inj₁ (neutral nf) = inj₁ (neutral (n-app nf))
    ... | inj₁ (canonical cf) with canonical-pi-value {v = f} (⇐-infer p (Conversion.≈-refl conv)) cf
    ...   | g′ , d′ , b , refl with progress⇒ q fa
    ...     | inj₂ (a′ , step) = inj₂ (tm-app (tm-lam g′ d′ b) a′ , ξ-app₂ step)
    ...     | inj₁ _ = inj₂ (substTopT a b , β)

    -- let: reduce the value, then ζ.
    progress⇒ (⇒-let {v = v} {b = b} p q r) (f-let fty fv fb) with progress⇐ q fv
    ... | inj₂ (v′ , step) = inj₂ (tm-let _ _ v′ b , ξ-let step)
    ... | inj₁ _ = inj₂ (substTopT v b , ζ)

    -- global: δ-unfold if the signature supplies a body, else an opaque neutral.
    progress⇒ (⇒-global {f = f} p) ff with Signature.body sig f in eq
    ... | just body′ = inj₂ (body′ , δ eq)
    ... | nothing = inj₁ (neutral n-global)

    -- case: reduce the scrutinee, then ι (peeling a literal scrutinee).
    progress⇒ (⇒-case {s = s} {m = m} {brs = brs} p q r covered) (f-case fs fm fbs) with progress⇒ p fs
    ... | inj₂ (s′ , step) = inj₂ (tm-case s′ m brs , ξ-case step)
    ... | inj₁ (neutral ns) = inj₁ (neutral (n-case ns))
    ... | inj₁ (canonical cs) with canonical-ctor {v = s} (⇐-infer p (Conversion.≈-refl conv)) cs
    ...   | inj₁ (c , args , refl) = case-ctor-step p covered
    ...   | inj₂ (inj₁ (k , refl)) = case-nat-step k brs m (nat-lit-family p) covered
    ...   | inj₂ (inj₂ (k , refl)) = case-bounded-step k brs m (bounded-lit-family p) covered

    -- Conversion on the inferred type: recurse on the same term.
    progress⇒ (⇒-conv der eq) ff = progress⇒ der ff
    progress⇒ (⇒-cumul der le) ff = progress⇒ der ff

    -- Checking cases.
    progress⇐ (⇐-lam p q) (f-lam fd fb) = inj₁ (canonical c-lam)
    progress⇐ (⇐-infer der eq) ff = progress⇒ der ff
    progress⇐ (⇐-conv der eq) ff = progress⇐ der ff
    progress⇐ (⇐-cumul der le) ff = progress⇒ der ff

  -- The public Progress lemma.
  progress :
    ∀ {t T}
    → Closed⊢ t T
    → Final t
    → Value t ⊎ (∃ λ t′ → _⇝_ sig t t′)
  progress = progress⇒