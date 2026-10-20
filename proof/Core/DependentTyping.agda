------------------------------------------------------------------------
-- Native replacement interfaces under review, NOT migrated soundness.
-- All declaration, argument, motive and branch derivations use ONE ind.
-- No base typing, ClosedFragmentSig, or preservation callback is used.
-- Motives have an ordinary typed curried contract: this is stricter than
-- executable fresh-value validation, not a refinement theorem for it.
------------------------------------------------------------------------
module Core.DependentTyping where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; length; reverse; map)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (Level; l0; succLevel; _≤ˡ_; _⊔ˡ_)
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Coverage using (CaseCoverage)
open import Core.Typing using (Ctx; ⟨⟩; extend; lookup; Conversion; surface-field-vars)
import Core.LocalFrame as F

-- Pure syntax shared by motive and branch rules. No typing assumption.
apps : Term → List Term → Term
apps function [] = function
apps function (arg ∷ args) = apps (tm-app function arg) args

-- A declaration telescope is opened FORWARDS, specialising its parameters
-- and protecting each preceding fresh field via extSub.
data Opened : ∀ {n m} → Ctx n → Sub → Telescope → Ctx m → Set where
  op[] : ∀ {n} {Γ : Ctx n} {σ} → Opened Γ σ [] Γ
  op∷ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ name T tele}
    → Opened (extend Γ (substS σ T)) (extSub σ) tele Δ
    → Opened Γ σ ((name , T) ∷ tele) Δ

-- The final body already lives under the whole telescope.
piTele : Sub → Telescope → Term → Term
piTele σ [] body = body
piTele σ ((name , T) ∷ tele) body =
  tm-pi unrestricted (substS σ T) (piTele (extSub σ) tele body)

motiveType : Family → List Term → Level → Term
motiveType family ps level =
  piTele (F.advance ps F.identity) (fam-indices family)
    (tm-pi unrestricted
      (tm-data (fam-name family)
        (map (shift (length (fam-indices family)) 0) ps)
        (surface-field-vars (length (fam-indices family))))
      (tm-type level))

branchGoal : Name → List Term → Ctor → Term → Term
branchGoal name ps ctor motive =
  apps (shift (length (ctor-args ctor)) 0 motive)
    (map (F.specializeParameters (length (ctor-args ctor)) ps) (ctor-indices ctor)
      ++ tm-ctor name (surface-field-vars (length (ctor-args ctor))) ∷ [])

parameterSlots : ℕ → ℕ → List Term
parameterSlots fields parameters =
  renameTerms (λ i → fields + i) (surface-field-vars parameters)

module Typing (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Conversion conv
  infix 4 _⊢_⇒_ _⊢_⇐_

  data _⊢_⇒_ : ∀ {n} → Ctx n → Term → Term → Set
  data _⊢_⇐_ : ∀ {n} → Ctx n → Term → Term → Set
  data WellFormed : ∀ {n} → Ctx n → Set
  data Declared : ∀ {n m} → Ctx n → Telescope → Ctx m → Set
  data Spine {n} (Γ : Ctx n) : List Term → List Term → Telescope → Set
  data Motive {n} (Γ : Ctx n) : Family → List Term → Term → Level → Set
  data Branches {n} (Γ : Ctx n) : Family → List Term → Term → List Branch → Set

  data _⊢_⇒_ where
    ⇒-type : ∀ {n} {Γ : Ctx n} {l l′} → succLevel l ≡ just l′
      → Γ ⊢ tm-type l ⇒ tm-type l′
    ⇒-var : ∀ {n} {Γ : Ctx n} (i : Fin n)
      → Γ ⊢ tm-var (toℕ i) ⇒ lookup Γ i
    ⇒-pi : ∀ {n} {Γ : Ctx n} {g d c i j}
      → Γ ⊢ d ⇒ tm-type i → extend Γ d ⊢ c ⇒ tm-type j
      → Γ ⊢ tm-pi g d c ⇒ tm-type (i ⊔ˡ j)
    ⇒-lam : ∀ {n} {Γ : Ctx n} {g d b l c}
      → Γ ⊢ d ⇒ tm-type l → extend Γ d ⊢ b ⇐ c
      → Γ ⊢ tm-lam g d b ⇒ tm-pi g d c
    ⇒-app : ∀ {n} {Γ : Ctx n} {f a g d c}
      → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ a ⇒ d
      → Γ ⊢ tm-app f a ⇒ substTopT a c
    ⇒-let : ∀ {n} {Γ : Ctx n} {g ty v b l T}
      → Γ ⊢ ty ⇒ tm-type l → Γ ⊢ v ⇐ ty → extend Γ ty ⊢ b ⇒ T
      → Γ ⊢ tm-let g ty v b ⇒ substTopT v T
    ⇒-global : ∀ {n} {Γ : Ctx n} {name T}
      → Signature.type-of sig name ≡ just T → Γ ⊢ tm-global name ⇒ T
    ⇒-int_type : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-int_type ⇒ tm-type l0
    ⇒-float_type : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-float_type ⇒ tm-type l0
    ⇒-binary_type : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-binary_type ⇒ tm-type l0
    ⇒-atom_type : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-atom_type ⇒ tm-type l0
    ⇒-int_lit : ∀ {n} {Γ : Ctx n} {k} → Γ ⊢ tm-int_lit k ⇒ tm-int_type
    ⇒-float_lit : ∀ {n} {Γ : Ctx n} → Γ ⊢ tm-float_lit ⇒ tm-float_type
    ⇒-atom_lit : ∀ {n} {Γ : Ctx n} {name} → Γ ⊢ tm-atom_lit name ⇒ tm-atom_type
    -- The legacy UNINDEXED builtin fragment only. Signature compatibility
    -- for literal peeling is a separate metatheory obligation, not inferred
    -- from the builtin name, nor an executable indexed-Bounded certificate.
    ⇒-nat_lit : ∀ {n} {Γ : Ctx n} {k name family}
      → IndEnv.builtins ind "nat" ≡ just name
      → findFamily name (IndEnv.families ind) ≡ just family
      → fam-params family ≡ [] → fam-indices family ≡ []
      → Γ ⊢ tm-nat_lit k ⇒ tm-data name [] []
    ⇒-bounded_lit : ∀ {n} {Γ : Ctx n} {k name family}
      → IndEnv.builtins ind "bounded" ≡ just name
      → findFamily name (IndEnv.families ind) ≡ just family
      → fam-params family ≡ [] → fam-indices family ≡ []
      → Γ ⊢ tm-bounded_lit k ⇒ tm-data name [] []
    ⇒-data : ∀ {n} {Γ : Ctx n} {name ps is family}
      → findFamily name (IndEnv.families ind) ≡ just family
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) is (fam-indices family)
      → Γ ⊢ tm-data name ps is ⇒ tm-type (fam-level family)
    -- ps is a DECLARATIVE witness, absent from the fields-only runtime
    -- constructor. It is not inferred by an algorithm or added to arity.
    ⇒-ctor : ∀ {n} {Γ : Ctx n} {name ps args family ctor}
      → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) args (ctor-args ctor)
      → Γ ⊢ tm-ctor name args ⇒ tm-data (fam-name family) ps
          (F.instantiateResults ps args (ctor-indices ctor))
    ⇒-case : ∀ {n} {Γ : Ctx n} {s motive brs name ps is family l}
      → WellFormed Γ
      → findFamily name (IndEnv.families ind) ≡ just family
      → Γ ⊢ s ⇒ tm-data name ps is
      → Spine Γ [] ps (fam-params family)
      → Spine Γ (reverse ps) is (fam-indices family)
      → Motive Γ family ps motive l
      → Branches Γ family ps motive brs
      → CaseCoverage ind name brs
      → Γ ⊢ tm-case s motive brs ⇒ apps motive (is ++ s ∷ [])
    ⇒-effect_type : ∀ {n} {Γ : Ctx n} {t l}
      → Γ ⊢ t ⇒ tm-type l → Γ ⊢ tm-effect_type t ⇒ tm-type l
    ⇒-effect_pure : ∀ {n} {Γ : Ctx n} {a A}
      → Γ ⊢ a ⇒ A → Γ ⊢ tm-effect_pure a ⇒ tm-effect_type A
    ⇒-effect_bind : ∀ {n} {Γ : Ctx n} {e k A B}
      → Γ ⊢ e ⇒ tm-effect_type A
      → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type (rename wk B))
      → Γ ⊢ tm-effect_bind e k ⇒ tm-effect_type B
    ⇒-conv : ∀ {n} {Γ : Ctx n} {t T T′}
      → Γ ⊢ t ⇒ T → T ≈ T′ → Γ ⊢ t ⇒ T′
    ⇒-cumul : ∀ {n} {Γ : Ctx n} {t i j}
      → Γ ⊢ t ⇒ tm-type i → i ≤ˡ j → Γ ⊢ t ⇒ tm-type j

  data _⊢_⇐_ where
    ⇐-lam : ∀ {n} {Γ : Ctx n} {g d b c l}
      → Γ ⊢ d ⇒ tm-type l → extend Γ d ⊢ b ⇐ c
      → Γ ⊢ tm-lam g d b ⇐ tm-pi g d c
    ⇐-hole : ∀ {n} {Γ : Ctx n} {name T} → Γ ⊢ tm-hole name ⇐ T
    ⇐-infer : ∀ {n} {Γ : Ctx n} {t T T′}
      → Γ ⊢ t ⇒ T′ → T′ ≈ T → Γ ⊢ t ⇐ T
    ⇐-conv : ∀ {n} {Γ : Ctx n} {t T T′}
      → Γ ⊢ t ⇐ T → T ≈ T′ → Γ ⊢ t ⇐ T′
    ⇐-cumul : ∀ {n} {Γ : Ctx n} {t i j}
      → Γ ⊢ t ⇒ tm-type i → i ≤ˡ j → Γ ⊢ t ⇐ tm-type j

  data WellFormed where
    wf[] : WellFormed ⟨⟩
    wf∷ : ∀ {n} {Γ : Ctx n} {T l}
      → WellFormed Γ → Scoped n T → Γ ⊢ T ⇒ tm-type l
      → WellFormed (extend Γ T)

  data Declared where
    dt[] : ∀ {n} {Γ : Ctx n} → Declared Γ [] Γ
    dt∷ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {name T tele l}
      → Scoped n T → Γ ⊢ T ⇒ tm-type l
      → Declared (extend Γ T) tele Δ
      → Declared Γ ((name , T) ∷ tele) Δ

  data Spine {n} Γ where
    sp[] : ∀ {locals} → Spine Γ locals [] []
    sp∷ : ∀ {locals arg args name T tele}
      → Γ ⊢ arg ⇐ F.instantiatePrefix locals T
      → Spine Γ (arg ∷ locals) args tele
      → Spine Γ locals (arg ∷ args) ((name , T) ∷ tele)

  data Motive {n} Γ where
    motive : ∀ {family ps m l u}
      → Scoped n m
      → Γ ⊢ motiveType family ps l ⇒ tm-type u
      → Γ ⊢ m ⇒ motiveType family ps l
      → Motive Γ family ps m l

  data Branches {n} Γ where
    br[] : ∀ {family ps motive} → Branches Γ family ps motive []
    br∷ : ∀ {m} {Δ : Ctx m} {family ps motive name ctor owner b brs}
      → findCtor name (IndEnv.families ind) ≡ just (owner , ctor)
      → owner ≡ family
      → Opened Γ (F.advance ps F.identity) (ctor-args ctor) Δ
      → WellFormed Δ
      → Δ ⊢ b ⇐ branchGoal name ps ctor motive
      → Branches Γ family ps motive brs
      → Branches Γ family ps motive ((name , length (ctor-args ctor) , b) ∷ brs)

  spine-length : ∀ {n} {Γ : Ctx n} {locals args tele}
    → Spine Γ locals args tele → length args ≡ length tele
  spine-length sp[] = refl
  spine-length (sp∷ arg rest) = cong suc (spine-length rest)

  LevelsBelow : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {tele}
    → Level → Declared Γ tele Δ → Set
  LevelsBelow cap dt[] = ⊤
  LevelsBelow cap (dt∷ {l = l} scoped kind rest) = l ≤ˡ cap × LevelsBelow cap rest

  record FamilyDeclaration (family : Family) : Set where
    field
      {p i} : ℕ
      parameter-context : Ctx p
      index-context : Ctx i
      parameters : Declared ⟨⟩ (fam-params family) parameter-context
      indices : Declared parameter-context (fam-indices family) index-context

  record ConstructorDeclaration (family : Family) (ctor : Ctor) : Set where
    field
      {p f} : ℕ
      parameter-context : Ctx p
      field-context : Ctx f
      parameters : Declared ⟨⟩ (fam-params family) parameter-context
      fields : Declared parameter-context (ctor-args ctor) field-context
      field-levels : LevelsBelow (fam-level family) fields
      result-scoping : ScopedTerms f (ctor-params ctor) × ScopedTerms f (ctor-indices ctor)
      uniform-parameters : ctor-params ctor ≡
        parameterSlots (length (ctor-args ctor)) (length (fam-params family))
      result-parameters : Spine field-context [] (ctor-params ctor) (fam-params family)
      result-indices : Spine field-context (reverse (ctor-params ctor))
        (ctor-indices ctor) (fam-indices family)

  -- Validity is separate from the mutually defined typing datatypes.
  -- It checks actual lookup entries using that SAME judgment. It is not
  -- a finite verifier or a proof of recursive positivity or termination.
  record SignatureValid : Set where
    field
      family-declared : ∀ {name family}
        → findFamily name (IndEnv.families ind) ≡ just family → FamilyDeclaration family
      constructor-declared : ∀ {name family ctor}
        → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
        → ConstructorDeclaration family ctor
      owner-visible : ∀ {name family ctor}
        → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
        → findFamily (fam-name family) (IndEnv.families ind) ≡ just family
      global-type : ∀ {name T} → Signature.type-of sig name ≡ just T
        → Scoped 0 T × (∃ λ l → ⟨⟩ ⊢ T ⇒ tm-type l)
      global-body : ∀ {name b} → Signature.body sig name ≡ just b
        → ∃ λ T → Signature.type-of sig name ≡ just T × Scoped 0 b × (⟨⟩ ⊢ b ⇒ T)

  -- A checked admission exposes validity and context/goal well-formedness.
  -- Finality/release eligibility remain separate, not inferred from holes
  -- being checkable. No native preservation/progress result is asserted.
  record Admitted {n} (Γ : Ctx n) (t T : Term) : Set where
    field
      signature-valid : SignatureValid
      context-valid : WellFormed Γ
      term-scoped : Scoped n t
      goal-scoped : Scoped n T
      goal-level : Level
      goal-kind : Γ ⊢ T ⇒ tm-type goal-level
      checked : Γ ⊢ t ⇐ T
