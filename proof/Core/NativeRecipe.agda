------------------------------------------------------------------------
-- Data-only recipe replay for a CASE-FREE native fragment.
-- A successful result contains a constructed native derivation; no
-- native proof, conversion witness or lookup callback is an input field.
-- Exact syntax checks are not NbE/eta or non-reflexive conversion.
------------------------------------------------------------------------
module Core.NativeRecipe where

open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Core.Syntax
open import Core.Grade using (Grade)
open import Core.Universe
  using (Level; l0; l1; l2; succLevel; _⊔ˡ_; _≤ˡ_; l≤-refl; l0≤l1; l0≤l2; l1≤l2)
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; ⟨⟩; extend; lookup; Conversion)
import Core.LocalFrame as Frame
import Core.DependentTyping as Native
import Core.SyntaxEquality as Syntax
import Core.NativeCertificate as Certificate
import Core.ExecutableSnapshot as Input
import Core.ExecutableReplay as Payloads
import Core.CanonicalSnapshot as S

data Recipe : Set where
  r-leaf : Recipe
  r-pi r-lam r-app : Recipe → Recipe → Recipe
  r-let : Recipe → Recipe → Recipe → Recipe
  r-data : List Recipe → List Recipe → Recipe
  r-ctor : List Term → List Recipe → List Recipe → Recipe
  r-claim : Term → Recipe → Recipe
  r-cumul : Level → Recipe → Recipe

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

module Derive (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  module N = Native.Typing ind sig conv

  Result : ∀ {n} → Ctx n → Term → Set
  Result Γ t = ∃ λ T → N._⊢_⇒_ Γ t T

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
  (payloads : Payloads.Replay.Payloads source metadata) (conv : Conversion) where
  module C = Certificate.Certificates source metadata payloads conv
  module D = Derive (S.Snapshot.ind C.R.snapshot) (S.Snapshot.sig C.R.snapshot) conv
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
