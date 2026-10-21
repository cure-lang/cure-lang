------------------------------------------------------------------------
-- Erasure: the structural core of the {0,ω} translation.
--
-- docs/SOUNDNESS.md §8.3 records that the soundness argument ASSUMES
-- `Erase.erase` drops only `:erased`-graded binders, but never proves that
-- erasure commutes with reduction. This module is the mechanised counterpart
-- of `lib/cure/elab/erase.ex`, so the property can be STATED — and, where it
-- holds, proved — rather than assumed.
--
-- SCOPE. This formalises structural recursion and let collapse:
--
--   * a let whose ERASED body is variable zero collapses to its erased
--     value; surviving lets have the unrestricted runtime grade;
--   * every other former recurses structurally, keeping constructor args;
--   * a bare `global` is left alone — erasure never performs δ.
--
-- `eraseSpine` separately filters a supplied quantity vector. `eraseTerm`
-- does not call it: signature lookup, arity guards, and application-spine
-- filtering are outside this model and outside `erase-idem`.
--
-- It deliberately does NOT model:
--
--   * the kernel's heuristic refinements (collapsible-family case
--     elimination, convoy discharge, the `cure_erased` placeholder). Those
--     are optimisations whose correctness is a separate obligation.
--
-- WHAT IS PROVED HERE (no postulates):
--
--   * `erase-idem` — structural erasure WITH let collapse is idempotent.
--     This is not a proof of idempotence of the full executable eraser.
--
-- WHAT IS *NOT* PROVED, and why (docs/SOUNDNESS.md §8.3):
--
--   * Executable erasure does NOT commute with δ. It drops arguments using
--     the CALLEE's declared quantities; after δ the callee is gone, so the
--     positions can no longer be identified. `Erase.erase/2` has no δ rule at
--     all, and the Elixir tests pin the concrete counterexample.
--   * Executable erasure's commutation with β/ζ/ι is NOT proved. General
--     substitution stability fails for the same reason δ commutation fails:
--     the quantities live in the SIGNATURE, not in the term.
------------------------------------------------------------------------
module Proof.Erase where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Core.Grade using (Grade; unrestricted; present?)
open import Core.Syntax
------------------------------------------------------------------------
-- Administrative identity elimination. Dispatch on the ERASED body: a
-- nested let can expose variable zero even when its original body is not
-- itself a variable. Surviving lets have the runtime unrestricted grade.
-- Keep this non-recursive dispatcher outside the erasure mutual block.
------------------------------------------------------------------------

isVar0 : Term → Bool
isVar0 (tm-var zero) = true
isVar0 _ = false

letStep : Bool → Term → Term → Term → Term
letStep true  ty v b = v
letStep false ty v b = tm-let unrestricted ty v b

------------------------------------------------------------------------
-- Erasure (mutually recursive over terms, term lists, and branches).
------------------------------------------------------------------------

mutual

  eraseTerm : Term → Term
  eraseTerm (tm-type l)          = tm-type l
  eraseTerm (tm-var k)           = tm-var k
  eraseTerm (tm-pi g d c)        = tm-pi g (eraseTerm d) (eraseTerm c)
  eraseTerm (tm-lam g d b)       = tm-lam g (eraseTerm d) (eraseTerm b)
  eraseTerm (tm-let g ty v b)    =
    letStep (isVar0 (eraseTerm b)) (eraseTerm ty) (eraseTerm v) (eraseTerm b)
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
-- Split the dispatcher BEFORE unfolding the outer erasure. In the false
-- branch, body fixedness aligns the second pass's test with the first.
-- No claim that erasure preserves a negative isVar0 test is needed.
letStep-fixed : ∀ flag ty v b
  → eraseTerm ty ≡ ty → eraseTerm v ≡ v → eraseTerm b ≡ b
  → isVar0 b ≡ flag
  → eraseTerm (letStep flag ty v b) ≡ letStep flag ty v b
letStep-fixed true ty v b ty-fixed v-fixed b-fixed test = v-fixed
letStep-fixed false ty v b ty-fixed v-fixed b-fixed test
  rewrite ty-fixed | v-fixed | b-fixed | test = refl

mutual

  eraseTerm-idem : ∀ t → eraseTerm (eraseTerm t) ≡ eraseTerm t
  eraseTerm-idem (tm-type l) = refl
  eraseTerm-idem (tm-var k) = refl
  eraseTerm-idem (tm-pi g d c) = cong₂ (tm-pi g) (eraseTerm-idem d) (eraseTerm-idem c)
  eraseTerm-idem (tm-lam g d b) = cong₂ (tm-lam g) (eraseTerm-idem d) (eraseTerm-idem b)
  eraseTerm-idem (tm-let g ty v b) =
    letStep-fixed (isVar0 (eraseTerm b)) (eraseTerm ty) (eraseTerm v) (eraseTerm b)
      (eraseTerm-idem ty) (eraseTerm-idem v) (eraseTerm-idem b) refl
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

------------------------------------------------------------------------
-- Definitional regressions. In particular, a nested non-variable body can
-- erase to variable zero: a negative isVar0 test is NOT preserved.
------------------------------------------------------------------------

erase-let-collapse : ∀ g ty v
  → eraseTerm (tm-let g ty v (tm-var zero)) ≡ eraseTerm v
erase-let-collapse g ty v = refl

erase-let-nested-collapse : ∀ g h ty inner-ty v
  → eraseTerm (tm-let g ty v (tm-let h inner-ty (tm-var zero) (tm-var zero)))
    ≡ eraseTerm v
erase-let-nested-collapse g h ty inner-ty v = refl

erase-let-survives : ∀ g ty v k
  → eraseTerm (tm-let g ty v (tm-var (suc k)))
    ≡ tm-let unrestricted (eraseTerm ty) (eraseTerm v) (tm-var (suc k))
erase-let-survives g ty v k = refl

nested-body-not-var0 : ∀ g ty
  → isVar0 (tm-let g ty (tm-var zero) (tm-var zero)) ≡ false
nested-body-not-var0 g ty = refl

erased-nested-body-is-var0 : ∀ g ty
  → isVar0 (eraseTerm (tm-let g ty (tm-var zero) (tm-var zero))) ≡ true
erased-nested-body-is-var0 g ty = refl
