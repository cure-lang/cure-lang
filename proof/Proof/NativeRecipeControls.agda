{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Rejection means failure of this bounded protocol, NOT refutation of
-- all native typing. EXACT-SYNTAX results can fail where a CHECKED
-- conversion recipe succeeds (the positive halves live in
-- Proof.NativeRecipeExamples); the controls below show that a conversion
-- recipe cannot be manufactured, guessed or used as an inference rule.
-- Cases still have no rule in this protocol.
------------------------------------------------------------------------
module Proof.NativeRecipeControls where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (linear; unrestricted)
open import Core.Universe using (l0; l1; l2)
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion)
open import Core.Reduction
open import Core.NativeRecipe
import Core.SyntaxEquality as Syntax
import Core.ExecutableSnapshot as Input
import Proof.ExecutableSnapshotExamples as Snapshot
import Proof.NativeCertificateExamples as Native
import Proof.NativeRecipeExamples as E
open E using (present)
module D = E.D

decision : ∀ {A : Set} → Dec A → Bool
decision (yes proof) = true
decision (no absent) = false

forged-type-claim : present
  (D.infer ⟨⟩ (tm-atom_lit "v") (r-claim tm-float_type r-leaf)) ≡ false
forged-type-claim = refl
correct-type-claim : present
  (D.infer ⟨⟩ (tm-atom_lit "v") (r-claim tm-atom_type r-leaf)) ≡ true
correct-type-claim = refl
wrong-grade-claim : present
  (D.infer ⟨⟩ (tm-lam linear tm-atom_type (tm-var 0))
    (r-claim (tm-pi unrestricted tm-atom_type tm-atom_type) (r-lam r-leaf r-leaf))) ≡ false
wrong-grade-claim = refl
escaped-lambda-variable : present
  (D.infer ⟨⟩ (tm-lam unrestricted tm-atom_type (tm-var 1)) (r-lam r-leaf r-leaf)) ≡ false
escaped-lambda-variable = refl
closed-free-variable : present (D.infer ⟨⟩ (tm-var 0) r-leaf) ≡ false
closed-free-variable = refl
ill-kinded-domain : present
  (D.infer ⟨⟩ (tm-lam unrestricted (tm-atom_lit "not-a-type") (tm-var 0))
    (r-lam r-leaf r-leaf)) ≡ false
ill-kinded-domain = refl
not-a-function : present
  (D.infer ⟨⟩ (tm-app (tm-atom_lit "f") (tm-atom_lit "a")) (r-app r-leaf r-leaf)) ≡ false
not-a-function = refl
wrong-rule : present (D.infer ⟨⟩ Native.value (r-lam r-leaf r-leaf)) ≡ false
wrong-rule = refl
unknown-global : present (D.infer ⟨⟩ (tm-global "missing") r-leaf) ≡ false
unknown-global = refl
unknown-family : present (D.infer ⟨⟩ (tm-data "missing" [] []) (r-data [] [])) ≡ false
unknown-family = refl
unknown-constructor : present (D.infer ⟨⟩ (tm-ctor "missing" []) (r-ctor [] [] [])) ≡ false
unknown-constructor = refl

missing-fields : present
  (D.infer ⟨⟩ (tm-ctor "Boundary#Pack" []) (r-ctor [] [] [])) ≡ false
missing-fields = refl
missing-field-recipe : present
  (D.infer ⟨⟩ Native.value (r-ctor [] [] (r-leaf ∷ []))) ≡ false
missing-field-recipe = refl
surplus-field-recipe : present
  (D.infer ⟨⟩ Native.value (r-ctor [] [] (r-leaf ∷ r-leaf ∷ r-leaf ∷ []))) ≡ false
surplus-field-recipe = refl
invented-parameter-witness : present
  (D.infer ⟨⟩ Native.value (r-ctor (tm-atom_type ∷ []) (r-leaf ∷ []) (r-leaf ∷ r-leaf ∷ []))) ≡ false
invented-parameter-witness = refl
missing-data-index : present
  (D.infer ⟨⟩ (tm-data "Boundary#Packed" [] []) (r-data [] [])) ≡ false
missing-data-index = refl

upward-cumulativity : present (D.at ⟨⟩ (tm-type l0) (tm-type l2) (r-cumul l2 r-leaf)) ≡ true
upward-cumulativity = refl
downward-cumulativity : present (D.infer ⟨⟩ (tm-type l1) (r-cumul l1 r-leaf)) ≡ false
downward-cumulativity = refl
ceiling-not-inferred : present (D.infer ⟨⟩ (tm-type l2) r-leaf) ≡ false
ceiling-not-inferred = refl
literal-not-a-kind : present (D.kind ⟨⟩ (tm-atom_lit "v") r-leaf) ≡ false
literal-not-a-kind = refl
holes-not-inferred : present (D.infer ⟨⟩ (tm-hole "h") (r-claim tm-atom_type r-leaf)) ≡ false
holes-not-inferred = refl
effects-not-inferred : present
  (D.infer ⟨⟩ (tm-effect_pure (tm-atom_lit "v")) r-leaf) ≡ false
effects-not-inferred = refl

dropped-hidden-body : present (E.G.replay Snapshot.raw-held (packet r-leaf nothing)) ≡ false
dropped-hidden-body = refl
opaque-entry : Input.GlobalInput
opaque-entry = record Snapshot.raw-held { body = nothing }
surplus-body-recipe : present (E.G.replay opaque-entry E.scalar-packet) ≡ false
surplus-body-recipe = refl
opaque-kind-only : present (E.G.replay opaque-entry (packet r-leaf nothing)) ≡ true
opaque-kind-only = refl
wrong-hidden-goal : present
  (E.G.replay (record Snapshot.raw-held { type = tm-float_type }) E.scalar-packet) ≡ false
wrong-hidden-goal = refl
forged-kind : present
  (E.G.replay Snapshot.raw-answer (packet (r-claim (tm-type l2) r-leaf) (just r-leaf))) ≡ false
forged-kind = refl

-- No recipe tag or asserted type can launder an unsupported case node.
case-never-replayed : ∀ {n} (Γ : Ctx n) s m bs recipe
  → D.infer Γ (tm-case s m bs) recipe ≡ nothing
case-never-replayed Γ s m bs r-leaf = refl
case-never-replayed Γ s m bs (r-pi a b) = refl
case-never-replayed Γ s m bs (r-lam a b) = refl
case-never-replayed Γ s m bs (r-app a b) = refl
case-never-replayed Γ s m bs (r-let a b c) = refl
case-never-replayed Γ s m bs (r-data ps is) = refl
case-never-replayed Γ s m bs (r-ctor ps prs ars) = refl
case-never-replayed Γ s m bs (r-claim claimed child)
  rewrite case-never-replayed Γ s m bs child = refl
case-never-replayed Γ s m bs (r-cumul target child)
  rewrite case-never-replayed Γ s m bs child = refl
case-never-replayed Γ s m bs (r-convert target conversion child)
  rewrite case-never-replayed Γ s m bs child = refl

beta-type : Term
beta-type = tm-app (tm-lam unrestricted tm-atom_type tm-atom_type) (tm-atom_lit "argument")
-- EXACT-SYNTAX replay still fails on a β-converted goal, even though the
-- same goal replays once a checked conversion recipe is supplied
-- (E.beta-goal-replayed). Exactness is a restriction, not a refutation.
beta-goal-not-replayed : present (D.at ⟨⟩ (tm-atom_lit "v") beta-type r-leaf) ≡ false
beta-goal-not-replayed = refl
native-beta-goal-exists : Native.N._⊢_⇒_ ⟨⟩ (tm-atom_lit "v") beta-type
native-beta-goal-exists = Native.N.⇒-conv Native.N.⇒-atom_lit
  (Conversion.≈-sym Native.conv {t = beta-type} {u = tm-atom_type}
    (Snapshot.ConversionModel.reduce-converts {t = beta-type} {u = tm-atom_type} β))

function-type eta-term : Term
function-type = tm-pi unrestricted tm-atom_type tm-atom_type
eta-term = tm-lam unrestricted tm-atom_type (tm-app (tm-var 1) (tm-var 0))
eta-syntax-distinct : decision (Syntax.equal? eta-term (tm-var 0)) ≡ false
eta-syntax-distinct = refl
eta-term-typed : Native.N._⊢_⇒_ (extend ⟨⟩ function-type) eta-term function-type
eta-term-typed = E.require
  (D.at (extend ⟨⟩ function-type) eta-term function-type (r-lam r-leaf (r-app r-leaf r-leaf))) refl

unequal-universes : decision (Syntax.equal? (tm-type l0) (tm-type l1)) ≡ false
unequal-universes = refl
unequal-grades : decision
  (Syntax.equal? (tm-pi linear tm-atom_type tm-atom_type) function-type) ≡ false
unequal-grades = refl
unequal-holes : decision (Syntax.equal? (tm-hole "a") (tm-hole "b")) ≡ false
unequal-holes = refl
unequal-signs : decision (Syntax.equal? (tm-int_lit (pos 0)) (tm-int_lit (negsuc 0))) ≡ false
unequal-signs = refl
parameter-index-split-distinct : decision
  (Syntax.equal? (tm-data "D" (tm-atom_type ∷ []) []) (tm-data "D" [] (tm-atom_type ∷ []))) ≡ false
parameter-index-split-distinct = refl
branch-arity-distinct : decision
  (Syntax.equal? (tm-case (tm-var 0) tm-atom_type (("C" , 1 , tm-var 0) ∷ []))
    (tm-case (tm-var 0) tm-atom_type (("C" , 2 , tm-var 0) ∷ []))) ≡ false
branch-arity-distinct = refl
effect-nodes-distinct : decision
  (Syntax.equal? (tm-effect_type tm-atom_type) (tm-effect_pure tm-atom_type)) ≡ false
effect-nodes-distinct = refl
literal-not-structural-constructor : decision
  (Syntax.equal? (tm-nat_lit 0) (tm-ctor "Z" [])) ≡ false
literal-not-structural-constructor = refl

------------------------------------------------------------------------
-- CONVERSION RECIPE CONTROLS
--
-- A recipe names a DERIVATION; it can never assert one. Every failure
-- below is a failure of this bounded protocol to reconstruct a checked
-- `Conversion._≈_` derivation, not a refutation of the native judgment.
------------------------------------------------------------------------

-- β fires only on the redex, in the stated direction, at its own reduct.
beta-reverse-not-replayed : present (D.conversion tm-atom_type beta-type c-beta) ≡ false
beta-reverse-not-replayed = refl
beta-wrong-target : present (D.conversion beta-type tm-float_type c-beta) ≡ false
beta-wrong-target = refl
beta-not-a-redex : present (D.conversion tm-atom_type tm-atom_type c-beta) ≡ false
beta-not-a-redex = refl
zeta-wrong-target : present
  (D.conversion E.let-type (tm-type l0) c-zeta) ≡ false
zeta-wrong-target = refl

-- Congruence rules check the ACTUAL structure: grades, family names,
-- constructor names and spine lengths are never inferred from the recipe.
pi-grade-mismatch : present
  (D.conversion (tm-pi unrestricted tm-atom_type tm-atom_type)
    (tm-pi linear tm-atom_type tm-atom_type) (c-pi c-refl c-refl)) ≡ false
pi-grade-mismatch = refl
app-not-an-application : present
  (D.conversion tm-atom_type tm-atom_type (c-app c-refl c-refl)) ≡ false
app-not-an-application = refl
data-name-mismatch : present
  (D.conversion (tm-data "Boundary#Packed" [] (tm-atom_type ∷ []))
    (tm-data "Other#Packed" [] (tm-atom_type ∷ []))
    (c-data [] (c-refl ∷ []))) ≡ false
data-name-mismatch = refl
data-spine-arity-mismatch : present
  (D.conversion (tm-data "Boundary#Packed" [] (tm-atom_type ∷ []))
    (tm-data "Boundary#Packed" [] (tm-atom_type ∷ [])) (c-data [] [])) ≡ false
data-spine-arity-mismatch = refl
ctor-spine-arity-mismatch : present
  (D.conversion (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "p" ∷ []))
    (tm-ctor "Boundary#Pack" (tm-atom_type ∷ tm-atom_lit "p" ∷ []))
    (c-ctor (c-refl ∷ []))) ≡ false
ctor-spine-arity-mismatch = refl

-- Transitivity names an intermediate term, and BOTH halves are checked
-- against it. A disconnected middle term is not a proof.
trans-disconnected : present
  (D.conversion E.let-type beta-type
    (c-trans tm-float_type c-zeta (c-sym c-beta))) ≡ false
trans-disconnected = refl
trans-missing-half : present
  (D.conversion E.let-type beta-type
    (c-trans tm-atom_type c-zeta c-beta)) ≡ false
trans-missing-half = refl

-- Compact-literal identification is shape-exact: no arithmetic, no
-- successor guessing, and no folding of a mutable bound.
nat-zero-not-successor : present
  (D.conversion (tm-ctor "S" (tm-nat_lit 0 ∷ [])) (tm-nat_lit 0) c-nat-zero) ≡ false
nat-zero-not-successor = refl
nat-suc-wrong-successor : present
  (D.conversion (tm-ctor "S" (tm-nat_lit 0 ∷ [])) (tm-nat_lit 2) c-nat-suc) ≡ false
nat-suc-wrong-successor = refl
bounded-suc-unmatched-bound : present
  (D.conversion (tm-ctor "Next" (tm-nat_lit 0 ∷ tm-bounded_lit 1 ∷ []))
    (tm-bounded_lit 1) c-bounded-suc) ≡ false
bounded-suc-unmatched-bound = refl

-- δ replay uses the ACTUAL signature table. An absent or non-visible body
-- does not unfold, and the unfolded body must be the asserted target.
delta-unknown-name : present
  (D.conversion (tm-global "missing") tm-atom_type (c-delta "missing")) ≡ false
delta-unknown-name = refl
delta-uncertified-body : present
  (D.conversion (tm-global "Boundary#held") (tm-atom_lit "hidden")
    (c-delta "Boundary#held")) ≡ false
delta-uncertified-body = refl
delta-wrong-target : present
  (D.conversion (tm-global "Boundary#answer") tm-atom_type
    (c-delta "Boundary#answer")) ≡ false
delta-wrong-target = refl
delta-wrong-name : present
  (D.conversion (tm-global "Boundary#answer") (tm-atom_lit "answer")
    (c-delta "Boundary#other")) ≡ false
delta-wrong-name = refl

-- A checked conversion cannot launder a WRONG goal: the dependent result
-- index really is the reduced form, so an unrelated index is rejected
-- even though the recipe is otherwise well-formed.
wrong-dependent-index : present
  (D.at ⟨⟩ E.computed-value (tm-data "Boundary#Packed" [] (tm-float_type ∷ []))
    (r-convert (tm-data "Boundary#Packed" [] (tm-atom_type ∷ []))
      (c-data [] (c-beta ∷ []))
      (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])))) ≡ false
wrong-dependent-index = refl
wrong-dependent-family : present
  (D.at ⟨⟩ E.computed-value (tm-data "Other#Packed" [] (tm-atom_type ∷ []))
    (r-convert (tm-data "Other#Packed" [] (tm-atom_type ∷ []))
      (c-data [] (c-beta ∷ []))
      (r-ctor [] [] (r-leaf ∷ r-leaf ∷ [])))) ≡ false
-- The asserted conversion target is data, so `at` still compares it with
-- the actual goal by exact syntax; a well-justified conversion to a
-- DIFFERENT type cannot be substituted for the goal.
conversion-target-not-goal : present
  (D.at ⟨⟩ (tm-atom_lit "v") tm-float_type
    (r-convert beta-type (c-sym c-beta) r-leaf)) ≡ false
conversion-target-not-goal = refl
wrong-dependent-family = refl

-- A type CLAIM is still compared by exact syntax; only `r-convert`
-- closes a goal under conversion, and only with a replayed derivation.
claim-not-closed-under-conversion : present
  (D.infer ⟨⟩ (tm-atom_lit "v") (r-claim beta-type r-leaf)) ≡ false
claim-not-closed-under-conversion = refl

-- Kind discovery THROUGH conversion is bounded by the replayed recipe:
-- the asserted sort must be the reduct the conversion actually reaches.
kind-wrong-sort : present
  (E.Alias.kind ⟨⟩ (tm-global "Alias#kind") (r-convert tm-float_type c-beta r-leaf))
  ≡ false
kind-wrong-sort = refl
kind-universe-inflation : present
  (E.Alias.kind ⟨⟩ (tm-global "Alias#kind") (r-convert (tm-type l1) c-beta r-leaf))
  ≡ false
kind-universe-inflation = refl

-- There is NO η rule: no recipe tag relates an η-expansion to its
-- neutral, so this record's construction cannot manufacture η even where
-- the executable `Conv` accepts it.
eta-not-conversion : present (D.conversion eta-term (tm-var 0) c-refl) ≡ false
eta-not-conversion = refl
eta-not-application-conversion : present
  (D.conversion eta-term (tm-var 0) (c-app c-refl c-refl)) ≡ false
eta-not-application-conversion = refl
