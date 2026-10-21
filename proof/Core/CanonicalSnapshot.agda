------------------------------------------------------------------------
-- Canonical finite views of the FORMAL registry.
-- Lookup agreement is derived, not supplied by a record field.
-- Elixir map extraction, atom/string encoding, aliases and metadata are
-- separate obligations. This is not a signature validity checker.
------------------------------------------------------------------------
module Core.CanonicalSnapshot where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Core.Syntax using (Name; Term)
open import Core.Signature
open import Core.Coverage using (lookup-ctor-members)
open import Core.Reduction using (Signature)

Table : Set → Set
Table A = List (Name × A)

lookup : ∀ {A} → Name → Table A → Maybe A
lookup key [] = nothing
lookup key ((name , value) ∷ rest) with key ≟ name
... | yes same = just value
... | no different = lookup key rest

orElse : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
orElse (just value) fallback = just value
orElse nothing fallback = fallback

lookup-append : ∀ {A} key (xs ys : Table A)
  → lookup key (xs ++ ys) ≡ orElse (lookup key xs) (lookup key ys)
lookup-append key [] ys = refl
lookup-append key ((name , value) ∷ xs) ys with key ≟ name
... | yes same = refl
... | no different = lookup-append key xs ys

lookup-head : ∀ {A} key (value : A) rest
  → lookup key ((key , value) ∷ rest) ≡ just value
lookup-head key value rest with key ≟ key
... | yes same = refl
... | no different = ⊥-elim (different refl)

data Fresh {A : Set} (key : Name) : Table A → Set where
  fresh[] : Fresh key []
  fresh∷ : ∀ {name value rest}
    → key ≢ name → Fresh key rest → Fresh key ((name , value) ∷ rest)

data Unique {A : Set} : Table A → Set where
  unique[] : Unique []
  unique∷ : ∀ {name value rest}
    → Fresh name rest → Unique rest → Unique ((name , value) ∷ rest)

fresh? : ∀ {A} (key : Name) (table : Table A) → Dec (Fresh key table)
fresh? key [] = yes fresh[]
fresh? key ((name , value) ∷ rest) with key ≟ name
... | yes same = no (λ { (fresh∷ different tail) → different same })
... | no different with fresh? key rest
... | yes tail = yes (fresh∷ different tail)
... | no absent = no (λ { (fresh∷ unequal tail) → absent tail })

unique? : ∀ {A} (table : Table A) → Dec (Unique table)
unique? [] = yes unique[]
unique? ((name , value) ∷ rest) with fresh? name rest
... | no absent = no (λ { (unique∷ fresh tail) → absent fresh })
... | yes fresh with unique? rest
... | yes tail = yes (unique∷ fresh tail)
... | no absent = no (λ { (unique∷ fresh tail) → absent tail })

fresh-misses : ∀ {A} {key} {table : Table A}
  → Fresh key table → lookup key table ≡ nothing
fresh-misses fresh[] = refl
fresh-misses {key = key} (fresh∷ {name = name} different rest) with key ≟ name
... | yes same = ⊥-elim (different same)
... | no unequal = fresh-misses rest

fresh-excludes : ∀ {A} {key value} {table : Table A}
  → Fresh key table → (key , value) ∈ table → Data.Empty.⊥
fresh-excludes (fresh∷ different rest) (here refl) = different refl
fresh-excludes (fresh∷ different rest) (there member) = fresh-excludes rest member

-- Membership implies lookup only under uniqueness. First-match behavior
-- itself remains defined for duplicates, allowing explicit audit controls.
member-lookup : ∀ {A} {key value} {table : Table A}
  → Unique table → (key , value) ∈ table → lookup key table ≡ just value
member-lookup (unique∷ {name = name} fresh unique) (here refl) =
  lookup-head name _ _
member-lookup {key = key} (unique∷ {name = name} fresh unique) (there member)
  with key ≟ name
... | yes refl = ⊥-elim (fresh-excludes fresh member)
... | no different = member-lookup unique member

lookup-member : ∀ {A} {key value} {table : Table A}
  → lookup key table ≡ just value → (key , value) ∈ table
lookup-member {table = []} ()
lookup-member {key = key} {table = (name , entry) ∷ rest} found with key ≟ name
... | yes refl with just-inj found
... | refl = here refl
lookup-member {table = (name , entry) ∷ rest} found | no different =
  there (lookup-member found)

familyTable : List Family → Table Family
familyTable [] = []
familyTable (family ∷ rest) = (fam-name family , family) ∷ familyTable rest

family-member-entry : ∀ {family families} → family ∈ families
  → (fam-name family , family) ∈ familyTable families
family-member-entry (here refl) = here refl
family-member-entry (there member) = there (family-member-entry member)

ownedConstructors : Family → List Ctor → Table (Family × Ctor)
ownedConstructors family [] = []
ownedConstructors family (ctor ∷ rest) =
  (ctor-name ctor , (family , ctor)) ∷ ownedConstructors family rest

constructorTable : List Family → Table (Family × Ctor)
constructorTable [] = []
constructorTable (family ∷ rest) =
  ownedConstructors family (fam-ctors family) ++ constructorTable rest

family-lookup-agrees : ∀ key families
  → lookup key (familyTable families) ≡ findFamily key families
family-lookup-agrees key [] = refl
family-lookup-agrees key (family ∷ rest) with key ≟ fam-name family
... | yes refl = refl
... | no different = family-lookup-agrees key rest

owned-lookup-agrees : ∀ key family ctors
  → lookup key (ownedConstructors family ctors)
    ≡ Maybe.map (λ ctor → family , ctor) (findCtorIn key ctors)
owned-lookup-agrees key family [] = refl
owned-lookup-agrees key family (ctor ∷ rest) with key ≟ ctor-name ctor
... | yes refl = refl
... | no different = owned-lookup-agrees key family rest

constructor-lookup-agrees : ∀ key families
  → lookup key (constructorTable families) ≡ findCtor key families
constructor-lookup-agrees key [] = refl
constructor-lookup-agrees key (family ∷ rest)
  rewrite lookup-append key (ownedConstructors family (fam-ctors family))
    (constructorTable rest)
        | owned-lookup-agrees key family (fam-ctors family)
  with findCtorIn key (fam-ctors family)
... | just ctor = refl
... | nothing = constructor-lookup-agrees key rest

record Global : Set where
  constructor global
  field
    declared-type : Term
    visible-body : Maybe Term
open Global public

signature : Table Global → Signature
signature globals = record
  { type-of = λ key → Maybe.map declared-type (lookup key globals)
  ; body = λ key → Maybe._>>=_ (lookup key globals) visible-body }

global-type-found : ∀ {globals key entry}
  → lookup key globals ≡ just entry
  → Signature.type-of (signature globals) key ≡ just (declared-type entry)
global-type-found found = cong (Maybe.map declared-type) found

global-body-found : ∀ {globals key entry}
  → lookup key globals ≡ just entry
  → Signature.body (signature globals) key ≡ visible-body entry
global-body-found found = cong (λ entry → Maybe._>>=_ entry visible-body) found

record Snapshot : Set where
  field
    family-entries : List Family
    globals : Table Global
    family-keys : Unique (familyTable family-entries)
    constructor-keys : Unique (constructorTable family-entries)
    global-keys : Unique globals
  -- No builtin identities or opaque/quantity metadata are reconstructed.
  -- They must not be silently inferred from this canonical table view.
  ind : IndEnv
  ind = record { families = family-entries ; builtins = λ _ → nothing }
  sig : Signature
  sig = signature globals

  owner-visible : ∀ {name family ctor}
    → findCtor name family-entries ≡ just (family , ctor)
    → findFamily (fam-name family) family-entries ≡ just family
  owner-visible {name} {family} found =
    trans (sym (family-lookup-agrees (fam-name family) family-entries))
      (member-lookup family-keys
        (family-member-entry (proj₁ (lookup-ctor-members {c = name} {fs = family-entries} found))))
