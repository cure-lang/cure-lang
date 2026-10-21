------------------------------------------------------------------------
-- Representation eligibility, NOT algorithmic kernel admission.
-- Exact registered names; no aliases, compact literals, Int nodes,
-- payload-free Float literals, effects, holes or absurd terms.
-- Native typing and all semantic metadata obligations remain separate.
------------------------------------------------------------------------
module Core.AdmissionBoundary where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion)
import Core.Typing as Context
import Core.CanonicalSnapshot as S
import Core.DependentTyping as Native
import Proof.Progress as Final

module Fragment (snapshot : S.Snapshot) where
  open S.Snapshot snapshot

  mutual
    data Supported (depth : ℕ) : Term → Set where
      s-type : ∀ {l} → Supported depth (tm-type l)
      s-var : ∀ {k} → k < depth → Supported depth (tm-var k)
      s-pi : ∀ {g d c} → Supported depth d → Supported (suc depth) c
        → Supported depth (tm-pi g d c)
      s-lam : ∀ {g d b} → Supported depth d → Supported (suc depth) b
        → Supported depth (tm-lam g d b)
      s-let : ∀ {g ty v b}
        → Supported depth ty → Supported depth v → Supported (suc depth) b
        → Supported depth (tm-let g ty v b)
      s-app : ∀ {f a} → Supported depth f → Supported depth a
        → Supported depth (tm-app f a)
      s-data : ∀ {name family ps is}
        → S.lookup name (S.familyTable family-entries) ≡ just family
        → Terms depth ps → Terms depth is → Supported depth (tm-data name ps is)
      s-ctor : ∀ {name family ctor args}
        → S.lookup name (S.constructorTable family-entries) ≡ just (family , ctor)
        → Terms depth args → Supported depth (tm-ctor name args)
      s-case : ∀ {s m branches}
        → Supported depth s → Supported depth m → Branches depth branches
        → Supported depth (tm-case s m branches)
      s-global : ∀ {name entry}
        → S.lookup name globals ≡ just entry → Supported depth (tm-global name)
      s-float_type : Supported depth tm-float_type
      s-binary_type : Supported depth tm-binary_type
      s-atom_type : Supported depth tm-atom_type
      s-atom_lit : ∀ {name} → Supported depth (tm-atom_lit name)

    data Terms (depth : ℕ) : List Term → Set where
      s[] : Terms depth []
      s∷ : ∀ {t ts} → Supported depth t → Terms depth ts → Terms depth (t ∷ ts)

    data Branches (depth : ℕ) : List Branch → Set where
      b[] : Branches depth []
      b∷ : ∀ {name family ctor ar body rest}
        → S.lookup name (S.constructorTable family-entries) ≡ just (family , ctor)
        → ar ≡ length (ctor-args ctor)
        → Supported (depth + ar) body → Branches depth rest
        → Branches depth ((name , ar , body) ∷ rest)

  mutual
    scoped : ∀ {n t} → Supported n t → Scoped n t
    scoped s-type = sc-type
    scoped (s-var bound) = sc-var bound
    scoped (s-pi d c) = sc-pi (scoped d) (scoped c)
    scoped (s-lam d b) = sc-lam (scoped d) (scoped b)
    scoped (s-let ty v b) = sc-let (scoped ty) (scoped v) (scoped b)
    scoped (s-app f a) = sc-app (scoped f) (scoped a)
    scoped (s-data found ps is) = sc-data (scoped-terms ps) (scoped-terms is)
    scoped (s-ctor found args) = sc-ctor (scoped-terms args)
    scoped (s-case s m branches) = sc-case (scoped s) (scoped m) (scoped-branches branches)
    scoped (s-global found) = sc-global
    scoped s-float_type = sc-float_type
    scoped s-binary_type = sc-binary_type
    scoped s-atom_type = sc-atom_type
    scoped s-atom_lit = sc-atom_lit

    scoped-terms : ∀ {n ts} → Terms n ts → ScopedTerms n ts
    scoped-terms s[] = st[]
    scoped-terms (s∷ t ts) = st∷ (scoped t) (scoped-terms ts)

    scoped-branches : ∀ {n bs} → Branches n bs → ScopedBranches n bs
    scoped-branches b[] = sb[]
    scoped-branches (b∷ found arity body rest) =
      sb∷ (sbranch (scoped body)) (scoped-branches rest)

  mutual
    final : ∀ {n t} → Supported n t → Final.Final t
    final s-type = Final.f-type
    final (s-var bound) = Final.f-var
    final (s-pi d c) = Final.f-pi (final d) (final c)
    final (s-lam d b) = Final.f-lam (final d) (final b)
    final (s-let ty v b) = Final.f-let (final ty) (final v) (final b)
    final (s-app f a) = Final.f-app (final f) (final a)
    final (s-data found ps is) = Final.f-data (final-terms ps) (final-terms is)
    final (s-ctor found args) = Final.f-ctor (final-terms args)
    final (s-case s m branches) = Final.f-case (final s) (final m) (final-branches branches)
    final (s-global found) = Final.f-global
    final s-float_type = Final.f-float_type
    final s-binary_type = Final.f-binary_type
    final s-atom_type = Final.f-atom_type
    final s-atom_lit = Final.f-atom_lit

    final-terms : ∀ {n ts} → Terms n ts → Final.FinalTerms ts
    final-terms s[] = Final.ft[]
    final-terms (s∷ t ts) = Final.ft∷ (final t) (final-terms ts)

    final-branches : ∀ {n bs} → Branches n bs → Final.FinalBranches bs
    final-branches b[] = Final.fb[]
    final-branches (b∷ found arity body rest) =
      Final.fb∷ (final body) (final-branches rest)

  -- Telescope entries see only preceding binders, not the complete frame.
  data TelescopeSupported (depth : ℕ) : Telescope → Set where
    t[] : TelescopeSupported depth []
    t∷ : ∀ {name T rest} → Supported depth T
      → TelescopeSupported (suc depth) rest
      → TelescopeSupported depth ((name , T) ∷ rest)

  record ConstructorSupported (family : Family) (ctor : Ctor) : Set where
    field
      fields : TelescopeSupported (length (fam-params family)) (ctor-args ctor)
      result-parameters : Terms (length (ctor-args ctor) + length (fam-params family))
        (ctor-params ctor)
      result-indices : Terms (length (ctor-args ctor) + length (fam-params family))
        (ctor-indices ctor)

  record FamilySupported (family : Family) : Set where
    field
      parameters : TelescopeSupported 0 (fam-params family)
      indices : TelescopeSupported (length (fam-params family)) (fam-indices family)
      constructors : All (ConstructorSupported family) (fam-ctors family)

  BodySupported : Maybe Term → Set
  BodySupported nothing = ⊤
  BodySupported (just body) = Supported 0 body

  record GlobalSupported (entry : S.Global) : Set where
    field
      type : Supported 0 (S.declared-type entry)
      body : BodySupported (S.visible-body entry)

  record PayloadsSupported : Set where
    field
      declarations : All FamilySupported family-entries
      definitions : All (λ entry → GlobalSupported (Data.Product.proj₂ entry)) globals

  -- Context types are stored in global index convention, not as raw
  -- declaration domains; inspect them at the whole caller depth.
  ContextSupported : ∀ {n} → Ctx n → Set
  ContextSupported {n} Γ = (i : Fin n) → Supported n (Context.lookup Γ i)

  module Admission (conv : Conversion) where
    module N = Native.Typing ind sig conv

    record Eligible {n} (Γ : Ctx n) (t T : Term) : Set where
      field
        payloads : PayloadsSupported
        caller : ContextSupported Γ
        source : Supported n t
        goal : Supported n T
        native : N.Admitted Γ t T
      -- This projection is intentionally not a theorem constructing native
      -- typing from syntax or from an Elixir checker result.
      checked : N._⊢_⇐_ Γ t T
      checked = N.Admitted.checked native
      source-final : Final.Final t
      source-final = final source
