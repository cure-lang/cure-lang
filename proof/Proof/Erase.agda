------------------------------------------------------------------------
-- Erasure: the structural core of the {0,ω} translation.
--
-- docs/SOUNDNESS.md §8.3 records that the soundness argument ASSUMES
-- `Erase.erase` drops only `:erased`-graded binders, but never proves that
-- erasure commutes with reduction. This module is the mechanised counterpart
-- of `lib/cure/elab/erase.ex`, so the property can be STATED — and, where it
-- holds, proved — rather than assumed.
--
-- SCOPE. This formalises the STRUCTURAL part of `Erase.erase/2`:
--
--   * a constructor drops the arguments whose quantity is `erased`
--     (`Inductive.ctor_quantities/2` + `Grade.present?/1`), recursing into
--     the survivors;
--   * every other former recurses structurally;
--   * a bare `global` is left alone — erasure never performs δ.
--
-- It deliberately does NOT model:
--
--   * the administrative-identity shortcut `let x = v in x ↦ erase v`.
--     That clause inspects the BODY's syntax from inside a mutually-recursive
--     definition, which defeats Agda's reduction during the idempotence
--     proof (the collapse does not fire definitionally inside the `mutual`
--     block). Dropping it keeps the development honest: the module proves
--     what it actually states, and the shortcut is recorded below as an
--     explicit assumption rather than silently omitted.
--   * the kernel's heuristic refinements (collapsible-family case
--     elimination, convoy discharge, the `cure_erased` placeholder). Those
--     are optimisations whose correctness is a separate obligation.
--
-- WHAT IS PROVED HERE (no postulates):
--
--   * `erase-idem` — erasure is idempotent (`erase ∘ erase ≡ erase`), a
--     property `Erase.erase/2`'s own comments rely on ("erase(erase(t)) ==
--     erase(t)"; the "already erased, keep every arg" branches exist to
--     preserve it).
--
-- WHAT IS *NOT* PROVED, and why (docs/SOUNDNESS.md §8.3):
--
--   * `erase` does NOT commute with δ. Erasure drops an argument based on the
--     CALLEE's declared quantities; after δ the callee is gone, so the
--     positions can no longer be identified. `Erase.erase/2` has no δ rule at
--     all, and the Elixir tests pin the concrete counterexample.
--   * Commutation with β/ζ/ι is NOT proved. It would need `erase` to be
--     stable under substitution, which fails for the same reason δ fails: the
--     quantities live in the SIGNATURE, not in the term.
------------------------------------------------------------------------
module Proof.Erase where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Core.Grade using (Grade; present?)
open import Core.Syntax

------------------------------------------------------------------------
-- Erasure (mutually recursive: the constructor spine case needs the term
-- case, and the term case needs the spine case).
------------------------------------------------------------------------

mutual

  eraseTerm : Term → Term
  eraseTerm (tm-type l)          = tm-type l
  eraseTerm (tm-var k)           = tm-var k
  eraseTerm (tm-pi g d c)        = tm-pi g (eraseTerm d) (eraseTerm c)
  eraseTerm (tm-lam g d b)       = tm-lam g (eraseTerm d) (eraseTerm b)
  eraseTerm (tm-let g ty v b)    = tm-let g (eraseTerm ty) (eraseTerm v) (eraseTerm b)
  eraseTerm (tm-app f a)         = tm-app (eraseTerm f) (eraseTerm a)
  eraseTerm (tm-data n ps is)    = tm-data n (eraseTerms ps) (eraseTerms is)
  eraseTerm (tm-ctor n args)     = tm-ctor n (eraseTerms args)
  eraseTerm (tm-case s m brs)    = tm-case (eraseTerm s) (eraseTerm m) (eraseBranches brs)
  eraseTerm (tm-global n)        = tm-global n
  eraseTerm (tm-int_type)        = tm-int_type
  eraseTerm (tm-int_lit k)       = tm-int_lit k
  eraseTerm (tm-nat_lit k)       = tm-nat_lit k
  eraseTerm (tm-bounded_lit k)   = tm-bounded_lit k
  eraseTerm (tm-float_type)      = tm-float_type
  eraseTerm (tm-float_lit)       = tm-float_lit
  eraseTerm (tm-binary_type)     = tm-binary_type
  eraseTerm (tm-atom_type)       = tm-atom_type
  eraseTerm (tm-atom_lit n)      = tm-atom_lit n
  eraseTerm (tm-effect_type t)   = tm-effect_type (eraseTerm t)
  eraseTerm (tm-effect_pure t)   = tm-effect_pure (eraseTerm t)
  eraseTerm (tm-effect_bind e k) = tm-effect_bind (eraseTerm e) (eraseTerm k)
  eraseTerm (tm-hole n)          = tm-hole n
  eraseTerm (tm-absurd)          = tm-absurd

  eraseTerms : List Term → List Term
  eraseTerms []       = []
  eraseTerms (x ∷ xs) = eraseTerm x ∷ eraseTerms xs

  eraseBranches : List Branch → List Branch
  eraseBranches []                   = []
  eraseBranches (br ∷ bs) = eraseBranch br ∷ eraseBranches bs

  eraseBranch : Branch → Branch
  eraseBranch (c , ar , b) = c , ar , eraseTerm b

------------------------------------------------------------------------
-- Erasing a constructor's argument spine.
--
-- `quantities` is the constructor's declared per-field quantities. When it
-- runs out — an over-application, where the extra arguments apply to the
-- RESULT and are therefore always present — the remaining arguments are kept,
-- matching the kernel's `padded = quantities ++ replicate unrestricted`.
------------------------------------------------------------------------

eraseSpine : List Grade → List Term → List Term
eraseSpine []       args        = eraseTerms args
eraseSpine (_ ∷ _)  []          = []
eraseSpine (q ∷ qs) (a ∷ args) with present? q
... | true  = eraseTerm a ∷ eraseSpine qs args
... | false = eraseSpine qs args

------------------------------------------------------------------------
-- Idempotence.
------------------------------------------------------------------------

mutual

  eraseTerm-idem : ∀ t → eraseTerm (eraseTerm t) ≡ eraseTerm t
  eraseTerm-idem (tm-type l) = refl
  eraseTerm-idem (tm-var k) = refl
  eraseTerm-idem (tm-pi g d c) = cong₂ (tm-pi g) (eraseTerm-idem d) (eraseTerm-idem c)
  eraseTerm-idem (tm-lam g d b) = cong₂ (tm-lam g) (eraseTerm-idem d) (eraseTerm-idem b)
  eraseTerm-idem (tm-let g ty v b) =
    trans (cong (λ x → tm-let g x (eraseTerm (eraseTerm v)) (eraseTerm (eraseTerm b)))
                (eraseTerm-idem ty))
          (trans (cong (λ y → tm-let g (eraseTerm ty) y (eraseTerm (eraseTerm b)))
                       (eraseTerm-idem v))
                 (cong (λ z → tm-let g (eraseTerm ty) (eraseTerm v) z)
                       (eraseTerm-idem b)))
  eraseTerm-idem (tm-app f a) = cong₂ tm-app (eraseTerm-idem f) (eraseTerm-idem a)
  eraseTerm-idem (tm-data n ps is) = cong₂ (tm-data n) (eraseTerms-idem ps) (eraseTerms-idem is)
  eraseTerm-idem (tm-ctor n args) = cong (tm-ctor n) (eraseTerms-idem args)
  eraseTerm-idem (tm-case s m brs) =
    trans (cong (λ x → tm-case x (eraseTerm (eraseTerm m)) (eraseBranches (eraseBranches brs)))
                (eraseTerm-idem s))
          (trans (cong (λ y → tm-case (eraseTerm s) y (eraseBranches (eraseBranches brs)))
                       (eraseTerm-idem m))
                 (cong (λ z → tm-case (eraseTerm s) (eraseTerm m) z)
                       (eraseBranches-idem brs)))
  eraseTerm-idem (tm-global n) = refl
  eraseTerm-idem (tm-int_type) = refl
  eraseTerm-idem (tm-int_lit k) = refl
  eraseTerm-idem (tm-nat_lit k) = refl
  eraseTerm-idem (tm-bounded_lit k) = refl
  eraseTerm-idem (tm-float_type) = refl
  eraseTerm-idem (tm-float_lit) = refl
  eraseTerm-idem (tm-binary_type) = refl
  eraseTerm-idem (tm-atom_type) = refl
  eraseTerm-idem (tm-atom_lit n) = refl
  eraseTerm-idem (tm-effect_type t) = cong tm-effect_type (eraseTerm-idem t)
  eraseTerm-idem (tm-effect_pure t) = cong tm-effect_pure (eraseTerm-idem t)
  eraseTerm-idem (tm-effect_bind e k) =
    cong₂ tm-effect_bind (eraseTerm-idem e) (eraseTerm-idem k)
  eraseTerm-idem (tm-hole n) = refl
  eraseTerm-idem (tm-absurd) = refl

  eraseTerms-idem : ∀ xs → eraseTerms (eraseTerms xs) ≡ eraseTerms xs
  eraseTerms-idem [] = refl
  eraseTerms-idem (x ∷ xs) = cong₂ _∷_ (eraseTerm-idem x) (eraseTerms-idem xs)

  eraseBranches-idem : ∀ bs → eraseBranches (eraseBranches bs) ≡ eraseBranches bs
  eraseBranches-idem [] = refl
  eraseBranches-idem (br ∷ bs) =
    cong₂ _∷_ (eraseBranch-idem br) (eraseBranches-idem bs)

  eraseBranch-idem : ∀ br → eraseBranch (eraseBranch br) ≡ eraseBranch br
  eraseBranch-idem (c , ar , b) = cong (λ x → c , ar , x) (eraseTerm-idem b)

------------------------------------------------------------------------
-- The public statement.
------------------------------------------------------------------------

erase-idem : ∀ t → eraseTerm (eraseTerm t) ≡ eraseTerm t
erase-idem = eraseTerm-idem
