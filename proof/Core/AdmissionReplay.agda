------------------------------------------------------------------------
-- Total proof-producing decisions for the EXISTING representation
-- grammar. These are not native typing or executable admission checks.
-- No conversion, coverage, declaration-kind or termination oracle.
------------------------------------------------------------------------
module Core.AdmissionReplay where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_) renaming (_<?_ to less?)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; length)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
import Core.Typing as C
import Core.CanonicalSnapshot as S
import Core.AdmissionBoundary as Boundary
import Proof.Progress as Final

all? : ∀ {A : Set} {P : A → Set} → ((x : A) → Dec (P x))
  → (xs : List A) → Dec (All.All P xs)
all? decide [] = yes All.[]
all? decide (x ∷ xs) with decide x
... | no absent = no (λ { (p All.∷ ps) → absent p })
... | yes p with all? decide xs
... | no absent = no (λ { (p All.∷ ps) → absent ps })
... | yes ps = yes (p All.∷ ps)

allFin? : ∀ {n} {P : Fin.Fin n → Set} → ((i : Fin.Fin n) → Dec (P i))
  → Dec ((i : Fin.Fin n) → P i)
allFin? {zero} decide = yes (λ ())
allFin? {suc n} decide with decide Fin.zero
... | no absent = no (λ p → absent (p Fin.zero))
... | yes first with allFin? {n} (λ i → decide (Fin.suc i))
... | no absent = no (λ p → absent (λ i → p (Fin.suc i)))
... | yes rest = yes (λ { Fin.zero → first ; (Fin.suc i) → rest i })

module Replay (snapshot : S.Snapshot) where
  open S.Snapshot snapshot using (family-entries; globals; sig)
  module B = Boundary.Fragment snapshot
  open B public

  missing : ∀ {A : Set} {key} {table : S.Table A} {entry}
    → S.lookup key table ≡ nothing → S.lookup key table ≡ just entry → ⊥
  missing absent found = nothing≠just (trans (sym absent) found)

  branch-view : ∀ {n name family ctor ar body rest}
    → S.lookup name (S.constructorTable family-entries) ≡ just (family , ctor)
    → Branches n ((name , ar , body) ∷ rest)
    → ar ≡ length (ctor-args ctor) × Supported (n + ar) body × Branches n rest
  branch-view selected (b∷ found arity body rest)
    with just-inj (trans (sym selected) found)
  ... | refl = arity , body , rest

  mutual
    supported? : (n : ℕ) (t : Term) → Dec (Supported n t)
    supported? n (tm-type l) = yes s-type
    supported? n (tm-var k) with less? k n
    ... | yes bound = yes (s-var bound)
    ... | no absent = no (λ { (s-var bound) → absent bound })
    supported? n (tm-pi g d c) with supported? n d
    ... | no absent = no (λ { (s-pi d c) → absent d })
    ... | yes d with supported? (suc n) c
    ... | no absent = no (λ { (s-pi d c) → absent c })
    ... | yes c = yes (s-pi d c)
    supported? n (tm-lam g d b) with supported? n d
    ... | no absent = no (λ { (s-lam d b) → absent d })
    ... | yes d with supported? (suc n) b
    ... | no absent = no (λ { (s-lam d b) → absent b })
    ... | yes b = yes (s-lam d b)
    supported? n (tm-let g ty v b) with supported? n ty
    ... | no absent = no (λ { (s-let ty v b) → absent ty })
    ... | yes ty with supported? n v
    ... | no absent = no (λ { (s-let ty v b) → absent v })
    ... | yes v with supported? (suc n) b
    ... | no absent = no (λ { (s-let ty v b) → absent b })
    ... | yes b = yes (s-let ty v b)
    supported? n (tm-app f a) with supported? n f
    ... | no absent = no (λ { (s-app f a) → absent f })
    ... | yes f with supported? n a
    ... | no absent = no (λ { (s-app f a) → absent a })
    ... | yes a = yes (s-app f a)
    supported? n (tm-data name ps is) with S.lookup name (S.familyTable family-entries) in selected
    ... | nothing = no (λ { (s-data found ps is) →
      missing {key = name} {table = S.familyTable family-entries} selected found })
    ... | just family with terms? n ps
    ... | no absent = no (λ { (s-data found ps is) → absent ps })
    ... | yes ps with terms? n is
    ... | no absent = no (λ { (s-data found ps is) → absent is })
    ... | yes is = yes (s-data selected ps is)
    supported? n (tm-ctor name args) with S.lookup name (S.constructorTable family-entries) in selected
    ... | nothing = no (λ { (s-ctor found args) →
      missing {key = name} {table = S.constructorTable family-entries} selected found })
    ... | just entry with terms? n args
    ... | no absent = no (λ { (s-ctor found args) → absent args })
    ... | yes args = yes (s-ctor selected args)
    supported? n (tm-case s m bs) with supported? n s
    ... | no absent = no (λ { (s-case s m bs) → absent s })
    ... | yes s with supported? n m
    ... | no absent = no (λ { (s-case s m bs) → absent m })
    ... | yes m with branches? n bs
    ... | no absent = no (λ { (s-case s m bs) → absent bs })
    ... | yes bs = yes (s-case s m bs)
    supported? n (tm-global name) with S.lookup name globals in selected
    ... | nothing = no (λ { (s-global found) → missing {key = name} {table = globals} selected found })
    ... | just entry = yes (s-global selected)
    supported? n tm-float_type = yes s-float_type
    supported? n tm-binary_type = yes s-binary_type
    supported? n tm-atom_type = yes s-atom_type
    supported? n (tm-atom_lit name) = yes s-atom_lit
    supported? n tm-int_type = no (λ ())
    supported? n (tm-int_lit k) = no (λ ())
    supported? n (tm-nat_lit k) = no (λ ())
    supported? n (tm-bounded_lit k) = no (λ ())
    supported? n tm-float_lit = no (λ ())
    supported? n (tm-effect_type t) = no (λ ())
    supported? n (tm-effect_pure t) = no (λ ())
    supported? n (tm-effect_bind e k) = no (λ ())
    supported? n (tm-hole name) = no (λ ())
    supported? n tm-absurd = no (λ ())

    terms? : (n : ℕ) (ts : List Term) → Dec (Terms n ts)
    terms? n [] = yes s[]
    terms? n (t ∷ ts) with supported? n t
    ... | no absent = no (λ { (s∷ t ts) → absent t })
    ... | yes t with terms? n ts
    ... | no absent = no (λ { (s∷ t ts) → absent ts })
    ... | yes ts = yes (s∷ t ts)

    branches? : (n : ℕ) (bs : List Branch) → Dec (Branches n bs)
    branches? n [] = yes b[]
    branches? n ((name , ar , body) ∷ rest)
      with S.lookup name (S.constructorTable family-entries) in selected
    ... | nothing = no (λ { (b∷ found arity body rest) →
      missing {key = name} {table = S.constructorTable family-entries} selected found })
    ... | just (family , ctor) with ar ≟ length (ctor-args ctor)
    ... | no absent = no (λ support → absent (proj₁ (branch-view selected support)))
    ... | yes arity with supported? (n + ar) body
    ... | no absent = no (λ support → absent (proj₁ (proj₂ (branch-view selected support))))
    ... | yes body with branches? n rest
    ... | no absent = no (λ { (b∷ found arity body rest) → absent rest })
    ... | yes rest = yes (b∷ selected arity body rest)

  telescope? : (n : ℕ) (tele : Telescope) → Dec (TelescopeSupported n tele)
  telescope? n [] = yes t[]
  telescope? n ((name , T) ∷ rest) with supported? n T
  ... | no absent = no (λ { (t∷ headSupport tailSupport) → absent headSupport })
  ... | yes headSupport with telescope? (suc n) rest
  ... | no absent = no (λ { (t∷ headSupport tailSupport) → absent tailSupport })
  ... | yes tailSupport = yes (t∷ headSupport tailSupport)

  constructor? : (family : Family) (ctor : Ctor) → Dec (ConstructorSupported family ctor)
  constructor? family ctor with telescope? (length (fam-params family)) (ctor-args ctor)
  ... | no absent = no (λ support → absent (ConstructorSupported.fields support))
  ... | yes fields with terms? (length (ctor-args ctor) + length (fam-params family)) (ctor-params ctor)
  ... | no absent = no (λ support → absent (ConstructorSupported.result-parameters support))
  ... | yes params with terms? (length (ctor-args ctor) + length (fam-params family)) (ctor-indices ctor)
  ... | no absent = no (λ support → absent (ConstructorSupported.result-indices support))
  ... | yes indices = yes record
    { fields = fields ; result-parameters = params ; result-indices = indices }

  family? : (family : Family) → Dec (FamilySupported family)
  family? family with telescope? 0 (fam-params family)
  ... | no absent = no (λ support → absent (FamilySupported.parameters support))
  ... | yes params with telescope? (length (fam-params family)) (fam-indices family)
  ... | no absent = no (λ support → absent (FamilySupported.indices support))
  ... | yes indices with all? (constructor? family) (fam-ctors family)
  ... | no absent = no (λ support → absent (FamilySupported.constructors support))
  ... | yes ctors = yes record { parameters = params ; indices = indices ; constructors = ctors }

  body? : (body : Data.Maybe.Maybe Term) → Dec (BodySupported body)
  body? nothing = yes tt
  body? (just body) = supported? 0 body

  global? : (entry : S.Global) → Dec (GlobalSupported entry)
  global? entry with supported? 0 (S.declared-type entry)
  ... | no absent = no (λ support → absent (GlobalSupported.type support))
  ... | yes typeSupport with body? (S.visible-body entry)
  ... | no absent = no (λ support → absent (GlobalSupported.body support))
  ... | yes bodySupport = yes record { type = typeSupport ; body = bodySupport }

  payloads? : Dec PayloadsSupported
  payloads? with all? family? family-entries
  ... | no absent = no (λ support → absent (PayloadsSupported.declarations support))
  ... | yes declarations with all? (λ entry → global? (proj₂ entry)) globals
  ... | no absent = no (λ support → absent (PayloadsSupported.definitions support))
  ... | yes definitions = yes record { declarations = declarations ; definitions = definitions }

  context? : ∀ {n} (Γ : C.Ctx n) → Dec (ContextSupported Γ)
  context? {n} Γ = allFin? (λ i → supported? n (C.lookup Γ i))

  visible-supported : ∀ {entry b} → GlobalSupported entry
    → S.visible-body entry ≡ just b → Supported 0 b
  visible-supported {S.global ty nothing} support ()
  visible-supported {S.global ty (just body)} support found with just-inj found
  ... | refl = GlobalSupported.body support

  body-supported : PayloadsSupported → ∀ {name b}
    → Signature.body sig name ≡ just b → Supported 0 b
  body-supported payloads {name} found with S.lookup name globals in selected
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just entry = visible-supported
    (All.lookup (PayloadsSupported.definitions payloads)
      (S.lookup-member {key = name} {table = globals} selected)) found

  type-supported : PayloadsSupported → ∀ {name T}
    → Signature.type-of sig name ≡ just T → Supported 0 T
  type-supported payloads {name} found with S.lookup name globals in selected
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just entry = subst (Supported 0) (just-inj found)
    (GlobalSupported.type (All.lookup (PayloadsSupported.definitions payloads)
      (S.lookup-member {key = name} {table = globals} selected)))

  bodies-closed : PayloadsSupported → ∀ {name b}
    → Signature.body sig name ≡ just b → Scoped 0 b
  bodies-closed payloads {name} found = scoped (body-supported payloads {name} found)

  bodies-final : PayloadsSupported → Final.BodiesFinal sig
  bodies-final payloads {name} found = final (body-supported payloads {name} found)

  types-closed : PayloadsSupported → ∀ {name T}
    → Signature.type-of sig name ≡ just T → Scoped 0 T
  types-closed payloads {name} found = scoped (type-supported payloads {name} found)
