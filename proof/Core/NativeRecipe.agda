------------------------------------------------------------------------
-- Data-only recipe replay for a CASE-FREE native fragment.
-- A successful result contains a constructed native derivation; no
-- native proof, lookup or conversion witness is an input field.
--
-- CONVERSION IS NOW REPLAYABLE AND CHECKED. Structural equality is still
-- what decides type ASSERTIONS, but `r-convert` reports an asserted
-- target when a conversion recipe reconstructs a derivation of the
-- abstract Conversion relation between that target and the type its child
-- actually synthesizes. The recipes are built from the record's own laws
-- plus ACTUAL β/ζ/δ steps of the ambient reduction relation. There is no
-- asserted-conversion constructor and no η, NbE, reduct or normalization
-- oracle: a recipe can only NAME a derivation the replayer reconstructs.
------------------------------------------------------------------------
module Core.NativeRecipe where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _,_)
import Data.String.Properties as String
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; trans)
open import Core.Syntax
open import Core.Grade using (Grade)
open import Core.Universe
  using (Level; l0; l1; l2; succLevel; _⊔ˡ_; _≤ˡ_; l≤-refl; l0≤l1; l0≤l2; l1≤l2)
open import Core.Signature
open import Core.Reduction using (Signature; _⇝_; β; ζ; δ)
open import Core.Typing
  using (Ctx; ⟨⟩; extend; lookup; Conversion; All2; a2[]; a2∷)
import Core.LocalFrame as Frame
import Core.DependentTyping as Native
import Core.SyntaxEquality as Syntax
import Core.NativeCertificate as Certificate
import Core.ExecutableSnapshot as Input
import Core.ExecutableReplay as Payloads
import Core.CanonicalSnapshot as S

------------------------------------------------------------------------
-- CONVERSION RECIPES — untrusted data, checked into a derivation.
--
-- Each constructor mirrors exactly one Conversion-record law or one
-- ACTUAL reduction rule of the ambient `_⇝_`. Consequently:
--
--   * `c-refl` is the only rule that can relate two terms without
--     inspecting them, so no recipe can assert a conversion;
--   * `c-beta`/`c-zeta` are the premise-free β/ζ rules, `c-delta` looks
--     its body up in the ACTUAL signature supplied to the replayer;
--   * `c-trans` names its intermediate term, which is itself untrusted:
--     both halves are checked against it;
--   * the compact-literal rules are the record's `≈-nat-*`/`≈-bounded-*`
--     identifications, not a decision procedure for literal equality;
--   * THERE IS NO η RULE. η conversion is not derivable here, so a goal
--     that needs it still fails this bounded protocol.
------------------------------------------------------------------------

data ConvRecipe : Set where
  c-refl : ConvRecipe
  c-sym : ConvRecipe → ConvRecipe
  c-trans : Term → ConvRecipe → ConvRecipe → ConvRecipe
  c-pi c-app : ConvRecipe → ConvRecipe → ConvRecipe
  c-data : List ConvRecipe → List ConvRecipe → ConvRecipe
  c-ctor : List ConvRecipe → ConvRecipe
  c-effect-type c-effect-pure : ConvRecipe → ConvRecipe
  c-effect-bind : ConvRecipe → ConvRecipe → ConvRecipe
  c-beta c-zeta : ConvRecipe
  c-delta : Name → ConvRecipe
  c-nat-zero c-bounded-zero c-nat-suc c-bounded-suc : ConvRecipe

data Recipe : Set where
  r-leaf : Recipe
  r-pi r-lam r-app : Recipe → Recipe → Recipe
  r-let : Recipe → Recipe → Recipe → Recipe
  r-data : List Recipe → List Recipe → Recipe
  r-ctor : List Term → List Recipe → List Recipe → Recipe
  r-claim : Term → Recipe → Recipe
  r-cumul : Level → Recipe → Recipe
  -- INFERENCE THROUGH A CHECKED CONVERSION. The child is replayed in
  -- inference mode; the ASSERTED target is reported only if the recipe
  -- reconstructs a conversion from the child's actual type to it. The
  -- target is untrusted data: it is checked, not assumed.
  r-convert : Term → ConvRecipe → Recipe → Recipe

record Packet : Set where
  constructor packet
  field
    kind-recipe : Recipe
    body-recipe : Maybe Recipe

index : (n k : ℕ) → Maybe (∃ λ (i : Fin.Fin n) → Fin.toℕ i ≡ k)
index zero k = nothing
index (suc n) zero = just (Fin.zero , refl)
index (suc n) (suc k) with index n k
... | nothing = nothing
... | just (i , equal) = just (Fin.suc i , cong suc equal)

level-le : (i j : Level) → Maybe (i ≤ˡ j)
level-le l0 l0 = just l≤-refl
level-le l0 l1 = just l0≤l1
level-le l0 l2 = just l0≤l2
level-le l1 l1 = just l≤-refl
level-le l1 l2 = just l1≤l2
level-le l2 l2 = just l≤-refl
level-le _ _ = nothing

-- Grades must agree SYNTACTICALLY for the Π congruence, which is why the
-- recipe carries no grade: only the context's own grades can be used.
grade-eq? : (g h : Grade) → Dec (g ≡ h)
grade-eq? g h with Nat._≟_ (Syntax.grade-number g) (Syntax.grade-number h)
... | yes same = yes
  (trans (sym (Syntax.grade-roundtrip g))
    (trans (cong Syntax.number-grade same) (Syntax.grade-roundtrip h)))
... | no different = no (λ { refl → different refl })

module Derive (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (reduce : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u) where
  module N = Native.Typing ind sig conv
  open Conversion conv

  Result : ∀ {n} → Ctx n → Term → Set
  Result Γ t = ∃ λ T → N._⊢_⇒_ Γ t T

  ----------------------------------------------------------------------
  -- Checked conversion replay.
  ----------------------------------------------------------------------

  mutual
    conversion : (t u : Term) → ConvRecipe → Maybe (t ≈ u)
    conversion t u c-refl with Syntax.equal? t u
    ... | no different = nothing
    ... | yes refl = just (≈-refl {t = t})
    conversion t u (c-sym recipe) with conversion u t recipe
    ... | nothing = nothing
    ... | just proof = just (≈-sym proof)
    conversion t u (c-trans middle first second) with conversion t middle first
    ... | nothing = nothing
    ... | just left with conversion middle u second
    ... | nothing = nothing
    ... | just right = just (≈-trans left right)
    conversion (tm-pi g d c) (tm-pi g′ d′ c′) (c-pi dom cod) with grade-eq? g g′
    ... | no different = nothing
    ... | yes refl with conversion d d′ dom | conversion c c′ cod
    ... | just d-proof | just c-proof = just (≈-pi d-proof c-proof)
    ... | _ | _ = nothing
    conversion _ _ (c-pi _ _) = nothing
    conversion (tm-app f a) (tm-app f′ a′) (c-app fun arg)
      with conversion f f′ fun | conversion a a′ arg
    ... | just f-proof | just a-proof = just (≈-app f-proof a-proof)
    ... | _ | _ = nothing
    conversion _ _ (c-app _ _) = nothing
    conversion (tm-data n ps is) (tm-data n′ ps′ is′) (c-data params indices)
      with String._≟_ n n′
    ... | no different = nothing
    ... | yes refl with spine-conversion ps ps′ params | spine-conversion is is′ indices
    ... | just p-proof | just i-proof = just (≈-data p-proof i-proof)
    ... | _ | _ = nothing
    conversion _ _ (c-data _ _) = nothing
    conversion (tm-ctor n args) (tm-ctor n′ args′) (c-ctor recipes)
      with String._≟_ n n′
    ... | no different = nothing
    ... | yes refl with spine-conversion args args′ recipes
    ... | nothing = nothing
    ... | just proof = just (≈-ctor proof)
    conversion _ _ (c-ctor _) = nothing
    conversion (tm-effect_type t) (tm-effect_type t′) (c-effect-type recipe)
      with conversion t t′ recipe
    ... | nothing = nothing
    ... | just proof = just (≈-effect_type proof)
    conversion _ _ (c-effect-type _) = nothing
    conversion (tm-effect_pure t) (tm-effect_pure t′) (c-effect-pure recipe)
      with conversion t t′ recipe
    ... | nothing = nothing
    ... | just proof = just (≈-effect_pure proof)
    conversion _ _ (c-effect-pure _) = nothing
    conversion (tm-effect_bind e k) (tm-effect_bind e′ k′) (c-effect-bind er kr)
      with conversion e e′ er | conversion k k′ kr
    ... | just e-proof | just k-proof = just (≈-effect_bind e-proof k-proof)
    ... | _ | _ = nothing
    conversion _ _ (c-effect-bind _ _) = nothing
    -- β: the only premise is the SYNTAX of the redex; the target must be
    -- the actual β-reduct, so a recipe cannot name another term.
    conversion (tm-app (tm-lam g d b) a) u c-beta with Syntax.equal? u (substTopT a b)
    ... | no different = nothing
    ... | yes refl = just (reduce (β {g = g} {d = d} {b = b} {a = a}))
    conversion _ _ c-beta = nothing
    conversion (tm-let g ty v b) u c-zeta with Syntax.equal? u (substTopT v b)
    ... | no different = nothing
    ... | yes refl = just (reduce (ζ {g = g} {ty = ty} {v = v} {b = b}))
    conversion _ _ c-zeta = nothing
    -- δ: replayed against the ACTUAL signature lookup, exactly like the
    -- global leaf. `found` is the checked equation, not recipe data.
    conversion (tm-global f) u (c-delta name) with String._≟_ f name
    ... | no different = nothing
    ... | yes refl with Signature.body sig f in found
    ... | nothing = nothing
    ... | just body with Syntax.equal? u body
    ...   | no different = nothing
    ...   | yes refl = just (reduce (δ {f = f} {body′ = body} found))
    conversion _ _ (c-delta _) = nothing
    conversion (tm-ctor "Z" []) (tm-nat_lit zero) c-nat-zero = just ≈-nat-zero
    conversion _ _ c-nat-zero = nothing
    conversion (tm-ctor "S" (tm-nat_lit k ∷ [])) (tm-nat_lit n) c-nat-suc
      with Nat._≟_ n (suc k)
    ... | no different = nothing
    ... | yes refl = just (≈-nat-suc {k = k})
    conversion _ _ c-nat-suc = nothing
    conversion (tm-ctor "First" (tm-nat_lit zero ∷ [])) (tm-bounded_lit n)
      c-bounded-zero with Nat._≟_ n zero
    ... | no different = nothing
    ... | yes refl = just ≈-bounded-zero
    conversion _ _ c-bounded-zero = nothing
    conversion (tm-ctor "Next" (tm-nat_lit k ∷ tm-bounded_lit m ∷ []))
      (tm-bounded_lit n) c-bounded-suc
      with Nat._≟_ m k | Nat._≟_ n (suc k)
    ... | no different | _ = nothing
    ... | yes refl | no different = nothing
    ... | yes refl | yes refl = just (≈-bounded-suc {k = k})
    conversion _ _ c-bounded-suc = nothing

    spine-conversion : (xs ys : List Term) → List ConvRecipe → Maybe (All2 _≈_ xs ys)
    spine-conversion [] [] [] = just a2[]
    spine-conversion (x ∷ xs) (y ∷ ys) (recipe ∷ recipes)
      with conversion x y recipe | spine-conversion xs ys recipes
    ... | just proof | just rest = just (a2∷ proof rest)
    ... | _ | _ = nothing
    spine-conversion _ _ _ = nothing

  ----------------------------------------------------------------------
  -- Native derivation replay.
  ----------------------------------------------------------------------

  leaf : ∀ {n} (Γ : Ctx n) (t : Term) → Maybe (Result Γ t)
  leaf Γ (tm-type l) with succLevel l in found
  ... | nothing = nothing
  ... | just level = just (tm-type level , N.⇒-type found)
  leaf {n} Γ (tm-var k) with index n k
  ... | nothing = nothing
  ... | just (i , equal) = just (lookup Γ i ,
    subst (λ k → N._⊢_⇒_ Γ (tm-var k) (lookup Γ i)) equal (N.⇒-var i))
  leaf Γ tm-atom_type = just (tm-type l0 , N.⇒-atom_type)
  leaf Γ tm-float_type = just (tm-type l0 , N.⇒-float_type)
  leaf Γ tm-binary_type = just (tm-type l0 , N.⇒-binary_type)
  leaf Γ (tm-atom_lit name) = just (tm-atom_type , N.⇒-atom_lit)
  leaf Γ (tm-global name) with Signature.type-of sig name in found
  ... | nothing = nothing
  ... | just T = just (T , N.⇒-global found)
  leaf Γ other = nothing

  mutual
    infer : ∀ {n} (Γ : Ctx n) (t : Term) → Recipe → Maybe (Result Γ t)
    infer Γ t r-leaf = leaf Γ t
    infer Γ t (r-claim claimed child) with at Γ t claimed child
    ... | nothing = nothing
    ... | just typed = just (claimed , typed)
    infer Γ t (r-cumul target child) with kind Γ t child
    ... | nothing = nothing
    ... | just (level , typed) with level-le level target
    ... | nothing = nothing
    ... | just le = just (tm-type target , N.⇒-cumul typed le)
    -- The asserted target is reported ONLY with a replayed conversion
    -- from the type the child actually synthesizes. A recipe that names
    -- the wrong target, or cannot justify the bridging steps, fails here.
    infer Γ t (r-convert target recipe sub) with infer Γ t sub
    ... | nothing = nothing
    ... | just (inferred , typed) with conversion inferred target recipe
    ... | nothing = nothing
    ... | just proof = just (target , N.⇒-conv typed proof)
    infer Γ (tm-pi grade domain codomain) (r-pi dr cr) with kind Γ domain dr
    ... | nothing = nothing
    ... | just (i , domain-typed) with kind (extend Γ domain) codomain cr
    ... | nothing = nothing
    ... | just (j , codomain-typed) =
      just (tm-type (i ⊔ˡ j) , N.⇒-pi domain-typed codomain-typed)
    infer Γ (tm-lam grade domain body) (r-lam dr br) with kind Γ domain dr
    ... | nothing = nothing
    ... | just (level , domain-typed) with infer (extend Γ domain) body br
    ... | nothing = nothing
    ... | just (codomain , body-typed) = just (tm-pi grade domain codomain ,
      N.⇒-lam domain-typed (N.⇐-infer body-typed (Conversion.≈-refl conv {t = codomain})))
    infer Γ (tm-app function argument) (r-app fr ar) with infer Γ function fr
    ... | nothing = nothing
    ... | just (tm-pi grade domain codomain , function-typed) with at Γ argument domain ar
    ... | nothing = nothing
    ... | just argument-typed =
      just (substTopT argument codomain , N.⇒-app function-typed argument-typed)
    infer Γ (tm-app function argument) (r-app fr ar) | just (other , typed) = nothing
    infer Γ (tm-let grade ty value body) (r-let tr vr br) with kind Γ ty tr
    ... | nothing = nothing
    ... | just (level , type-typed) with checking Γ value ty vr
    ... | nothing = nothing
    ... | just value-typed with infer (extend Γ ty) body br
    ... | nothing = nothing
    ... | just (T , body-typed) =
      just (substTopT value T , N.⇒-let type-typed value-typed body-typed)
    infer Γ (tm-data name ps is) (r-data prs irs) with findFamily name (IndEnv.families ind) in found
    ... | nothing = nothing
    ... | just family with spine Γ [] ps (fam-params family) prs
    ... | nothing = nothing
    ... | just params with spine Γ (reverse ps) is (fam-indices family) irs
    ... | nothing = nothing
    ... | just indices = just (tm-type (fam-level family) , N.⇒-data found params indices)
    infer Γ (tm-ctor name args) (r-ctor ps prs ars) with findCtor name (IndEnv.families ind) in found
    ... | nothing = nothing
    ... | just (family , ctor) with spine Γ [] ps (fam-params family) prs
    ... | nothing = nothing
    ... | just params with spine Γ (reverse ps) args (ctor-args ctor) ars
    ... | nothing = nothing
    ... | just arguments = just
      (tm-data (fam-name family) ps (Frame.instantiateResults ps args (ctor-indices ctor)) ,
        N.⇒-ctor found params arguments)
    infer Γ t recipe = nothing

    at : ∀ {n} (Γ : Ctx n) (t T : Term) → Recipe → Maybe (N._⊢_⇒_ Γ t T)
    at Γ t T recipe with infer Γ t recipe
    ... | nothing = nothing
    ... | just (inferred , typed) with Syntax.equal? inferred T
    ... | no unequal = nothing
    ... | yes refl = just typed

    checking : ∀ {n} (Γ : Ctx n) (t T : Term) → Recipe → Maybe (N._⊢_⇐_ Γ t T)
    checking Γ t T recipe with at Γ t T recipe
    ... | nothing = nothing
    ... | just typed = just (N.⇐-infer typed (Conversion.≈-refl conv {t = T}))

    kind : ∀ {n} (Γ : Ctx n) (t : Term) → Recipe
      → Maybe (∃ λ level → N._⊢_⇒_ Γ t (tm-type level))
    kind Γ t recipe with infer Γ t recipe
    ... | nothing = nothing
    ... | just (tm-type level , typed) = just (level , typed)
    ... | just (other , typed) = nothing

    spine : ∀ {n} (Γ : Ctx n) (locals args : List Term) (tele : Telescope)
      → List Recipe → Maybe (N.Spine Γ locals args tele)
    spine Γ locals [] [] [] = just N.sp[]
    spine Γ locals (arg ∷ args) ((name , T) ∷ tele) (recipe ∷ recipes)
      with checking Γ arg (Frame.instantiatePrefix locals T) recipe
    ... | nothing = nothing
    ... | just typed with spine Γ (arg ∷ locals) args tele recipes
    ... | nothing = nothing
    ... | just tail = just (N.sp∷ typed tail)
    spine Γ locals args tele recipes = nothing

module Globals (source : Input.Input) (metadata : Input.Accepted source)
  (payloads : Payloads.Replay.Payloads source metadata) (conv : Conversion)
  (reduce : ∀ {t u} → _⇝_ (S.Snapshot.sig (Payloads.Replay.snapshot source metadata)) t u
    → Conversion._≈_ conv t u) where
  module C = Certificate.Certificates source metadata payloads conv
  module D = Derive (S.Snapshot.ind C.R.snapshot) (S.Snapshot.sig C.R.snapshot) conv reduce
  body-proof : (goal : Term) (body : Maybe Term) → Maybe Recipe → Maybe (C.BodyTyped goal body)
  body-proof goal nothing nothing = just tt
  body-proof goal nothing (just recipe) = nothing
  body-proof goal (just body) nothing = nothing
  body-proof goal (just body) (just recipe) = D.at ⟨⟩ body goal recipe

  replay : (entry : Input.GlobalInput) → Packet → Maybe (C.GlobalEvidence entry)
  replay entry (packet kr br) with D.kind ⟨⟩ (Input.GlobalInput.type entry) kr
  ... | nothing = nothing
  ... | just (level , kind-typed) with body-proof (Input.GlobalInput.type entry) (Input.GlobalInput.body entry) br
  ... | nothing = nothing
  ... | just typed = just record { level = level ; kind = kind-typed ; body = typed }
