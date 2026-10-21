------------------------------------------------------------------------
-- Metadata-bearing replay model for the bounded executable exporter.
-- Acceptance checks layouts and unique finite keys, NOT declaration
-- typing, certificate semantics, syntax support or Elixir refinement.
------------------------------------------------------------------------
module Core.ExecutableSnapshot where

open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Core.Syntax
open import Core.Signature using (Ctor; Family)
open import Core.Grade using (Grade; erased; linear; affine; unrestricted)
open import Core.Universe using (Level)
import Core.CanonicalSnapshot as S

record ConstructorInput : Set where
  constructor constructor-input
  field
    declaration : Ctor
    quantities : List Grade
    explicit : List Bool
open ConstructorInput

record FamilyInput : Set where
  constructor family-input
  field
    name : Name
    parameters indices : Core.Signature.Telescope
    level : Level
    constructors : List ConstructorInput
    is-opaque : Bool
open FamilyInput

record GlobalInput : Set where
  constructor global-input
  field
    name : Name
    type : Term
    body : Maybe Term
    quantities : Maybe (List Grade)
    explicit : Maybe (List Bool)
    certified totality-certified : Bool
open GlobalInput

record Input : Set where
  constructor input
  field
    families : List FamilyInput
    globals : List GlobalInput
    builtins : S.Table Name
open Input

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all predicate [] = true
all predicate (x ∷ xs) = predicate x ∧ all predicate xs

unrestricted? : Grade → Bool
unrestricted? unrestricted = true
unrestricted? erased = false
unrestricted? linear = false
unrestricted? affine = false

constructor-layout : ConstructorInput → Bool
constructor-layout entry =
  (length (quantities entry) ≡ᵇ length (Core.Signature.ctor-args (declaration entry))) ∧
  (length (explicit entry) ≡ᵇ length (Core.Signature.ctor-args (declaration entry))) ∧
  all unrestricted? (quantities entry) ∧ all (λ x → x) (explicit entry)

family-layout : FamilyInput → Bool
family-layout entry = not (is-opaque entry) ∧ all constructor-layout (constructors entry)

pi-arity : Term → ℕ
pi-arity (tm-pi g d c) = suc (pi-arity c)
pi-arity other = zero

optional-layout : ∀ {A : Set} → (A → Bool) → ℕ → Maybe (List A) → Bool
optional-layout predicate count nothing = true
optional-layout predicate count (just values) =
  (length values ≡ᵇ count) ∧ all predicate values

has-body : Maybe Term → Bool
has-body nothing = false
has-body (just body) = true

global-layout : GlobalInput → Bool
global-layout entry =
  optional-layout unrestricted? (pi-arity (type entry)) (quantities entry) ∧
  optional-layout (λ x → x) (pi-arity (type entry)) (explicit entry) ∧
  (if certified entry then totality-certified entry ∧ has-body (body entry) else true)

no-builtins : S.Table Name → Bool
no-builtins [] = true
no-builtins (_ ∷ _) = false

metadata : Input → Bool
metadata source =
  no-builtins (builtins source) ∧ all family-layout (families source) ∧
  all global-layout (globals source)

project-family : FamilyInput → Family
project-family entry = record
  { fam-name = name entry ; fam-params = parameters entry ; fam-indices = indices entry
  ; fam-level = level entry ; fam-ctors = map declaration (constructors entry)
  -- Neither boolean is a certificate produced by this replay.
  ; positive = false ; universe-ok = false }

project-global : GlobalInput → S.Global
project-global entry = S.global (type entry)
  (if certified entry then body entry else nothing)

declared-type-preserved : ∀ entry → S.declared-type (project-global entry) ≡ type entry
declared-type-preserved entry = refl

uncertified-hidden : ∀ entry → certified entry ≡ false
  → S.visible-body (project-global entry) ≡ nothing
uncertified-hidden entry hidden rewrite hidden = refl

certified-visible : ∀ entry → certified entry ≡ true
  → S.visible-body (project-global entry) ≡ body entry
certified-visible entry visible rewrite visible = refl

family-entries : Input → List Family
family-entries source = map project-family (families source)

global-entries : Input → S.Table S.Global
global-entries source = map (λ entry → name entry , project-global entry) (globals source)

record Accepted (source : Input) : Set where
  field
    metadata-ok : metadata source ≡ true
    family-keys : S.Unique (S.familyTable (family-entries source))
    constructor-keys : S.Unique (S.constructorTable (family-entries source))
    global-keys : S.Unique (global-entries source)
  snapshot : S.Snapshot
  snapshot = record
    { family-entries = family-entries source ; globals = global-entries source
    ; family-keys = family-keys ; constructor-keys = constructor-keys ; global-keys = global-keys }

check : (source : Input) → Dec (Accepted source)
check source with metadata source in checked
... | false = no (λ accepted → false≠true (trans (sym checked) (Accepted.metadata-ok accepted)))
  where
  false≠true : false ≡ true → ⊥
  false≠true ()
... | true with S.unique? (S.familyTable (family-entries source))
... | no absent = no (λ accepted → absent (Accepted.family-keys accepted))
... | yes families-unique with S.unique? (S.constructorTable (family-entries source))
... | no absent = no (λ accepted → absent (Accepted.constructor-keys accepted))
... | yes constructors-unique with S.unique? (global-entries source)
... | no absent = no (λ accepted → absent (Accepted.global-keys accepted))
... | yes globals-unique = yes record
  { metadata-ok = checked ; family-keys = families-unique
  ; constructor-keys = constructors-unique ; global-keys = globals-unique }
