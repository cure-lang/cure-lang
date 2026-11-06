------------------------------------------------------------------------
-- M2b examples: a concrete adapter instance and the controls that keep
-- the construction from being vacuous.
--
-- `Core.AdapterConstruction` proves four representation obligations
-- from the adapter's DEFINITION rather than assuming them. A theorem
-- about a definition is only useful if the definition is inhabited and
-- if each hypothesis it relies on can actually fail, so this module
-- supplies both.
--
-- POSITIVE: a two-family payload is checked, its table extracted, and
-- every discharged obligation is exercised at a concrete name.
--
-- NEGATIVE: each hypothesis the construction RELIES ON is shown to be
-- load-bearing by exhibiting a payload that violates it.
------------------------------------------------------------------------
module Proof.AdapterConstructionExamples where

open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional as UniqueP using ()
open import Data.List.Relation.Unary.AllPairs.Core as AllPairs using ()
open import Data.List.Relation.Unary.All as All using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.String using (String; toList)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Core.Syntax using (Name)
open import Core.HostTable using (HostTable; Unique)
import Core.HostTable as HT
open import Core.AdapterConstruction

------------------------------------------------------------------------
-- A concrete payload: two families, one alias, one certified global.
------------------------------------------------------------------------

two-families : List String
two-families = "Boundary#Packed" ∷ "Boundary#Box" ∷ []

one-alias : List (String × String)
one-alias = ("Packed" , "Boundary#Packed") ∷ []

sample : Payload
sample = record
  { family-names = two-families
  ; global-names = "Boundary#id" ∷ []
  ; alias-pairs  = one-alias
  ; certified    = "Boundary#id" ∷ []
  ; totality     = "Boundary#id" ∷ []
  }

------------------------------------------------------------------------
-- (6) ORDER PRESERVED, at concrete names.
--
-- The extracted table resolves each family to ITSELF, and that is the
-- host's own first match. An absent name agrees too. These are `refl`
-- because both sides compute -- the agreement is definitional once the
-- extraction is defined, which is the whole point.
------------------------------------------------------------------------

order-packed : HT.host-key "Boundary#Packed" (extract-names two-families)
             ≡ host-first-match "Boundary#Packed" two-families
order-packed = order-preserved "Boundary#Packed" two-families

order-box : HT.host-key "Boundary#Box" (extract-names two-families)
          ≡ host-first-match "Boundary#Box" two-families
order-box = order-preserved "Boundary#Box" two-families

order-absent : HT.host-key "Nope" (extract-names two-families)
             ≡ host-first-match "Nope" two-families
order-absent = order-preserved "Nope" two-families

-- The concrete value, so the equation is not merely abstract.
order-absent-value : HT.host-key "Nope" (extract-names two-families) ≡ nothing
order-absent-value = refl

------------------------------------------------------------------------
-- (3) DUPLICATE REJECTION.
--
-- The `Checked` smart constructor requires distinctness. The positive
-- instance supplies it; the negative control shows that a payload with
-- a repeated family CANNOT satisfy the premise, so the obligation
-- cannot be bypassed by simply not looking.
------------------------------------------------------------------------

-- The two spellings differ, so an equality between them is refuted by
-- the mismatched character lists.
packed≠box : ¬ ("Boundary#Packed" ≡ "Boundary#Box")
packed≠box same = differing (cong toList same)
  where
    differing : toList "Boundary#Packed" ≡ toList "Boundary#Box" → ⊥
    differing ()

-- `NoDup` for the two-family list: the head differs from the one later
-- element, and the tail is trivially `NoDup`.
no-dup : NoDup two-families
no-dup = All._∷_ packed≠box All.[] , All.[] , tt

-- Distinctness of the two-family list, through the general lemma.
two-distinct : Distinct two-families
two-distinct = distinct-of-distinct two-families no-dup

-- The positive instance.
sample-checked : Checked
sample-checked = checked two-families two-distinct

-- The obligation, instantiated.
sample-unique : UniqueP.Unique (extract-string (host-names sample-checked))
sample-unique = duplicates-rejected sample-checked

-- NEGATIVE CONTROL: a repeated family violates the pairwise-inequality
-- premise, so no `Distinct` value exists for it.
repeated : List String
repeated = "Boundary#Packed" ∷ "Boundary#Packed" ∷ []

repeated-not-inequal : ¬ (∀ a b → a ∈ repeated → b ∈ repeated → a ≢ b)
repeated-not-inequal h =
  h "Boundary#Packed" "Boundary#Packed" (here refl) (here refl) refl

------------------------------------------------------------------------
-- (4) ALIAS SEPARATION.
--
-- The sample's alias points at a real family, so its KEY is absent from
-- the family list: the sources are disjoint and separation holds. The
-- negative control exhibits a payload whose alias key IS a family,
-- where separation fails -- which is exactly why the premise is needed
-- rather than discharged for free.
------------------------------------------------------------------------

-- The alias key `"Packed"` differs from both family spellings, so it is
-- not a family. Each membership case is refuted by the mismatched
-- character lists.
differing-packed : toList "Packed" ≡ toList "Boundary#Packed" → ⊥
differing-packed ()

differing-box : toList "Packed" ≡ toList "Boundary#Box" → ⊥
differing-box ()

packed-is-not-a-family : ¬ ("Packed" ∈ two-families)
packed-is-not-a-family (here same) = differing-packed (cong toList same)
packed-is-not-a-family (there (here same)) = differing-box (cong toList same)
packed-is-not-a-family (there (there ()))

sample-disjoint : SourcesDisjoint two-families one-alias
sample-disjoint key target (here refl) = packed-is-not-a-family
sample-disjoint key target (there ())

sample-separate : ∀ key target → (key , target) ∈ one-alias
  → ¬ ((key , target) ∈ extract-string two-families)
sample-separate = aliases-separate two-families one-alias sample-disjoint

-- NEGATIVE CONTROL: an alias whose key IS a family. Separation fails,
-- so no `SourcesDisjoint` value exists for it.
overlapping : List (String × String)
overlapping = ("Boundary#Packed" , "Boundary#Box") ∷ []

overlapping-not-disjoint : ¬ (SourcesDisjoint two-families overlapping)
overlapping-not-disjoint disjoint =
  disjoint "Boundary#Packed" "Boundary#Box" (here refl) (here refl)

------------------------------------------------------------------------
-- (8) SIGNATURE IMMUTABILITY, the version with content.
--
-- Two stages observing the SAME table agree. Two stages observing
-- DIFFERENT tables need not, which is what makes the hypothesis
-- load-bearing rather than decorative.
------------------------------------------------------------------------

sample-table : HostTable Name
sample-table = record { bindings = extract-names two-families ; aliases = [] }

same-table : ∀ name
  → HT.host-key name (HT.bindings sample-table)
  ≡ HT.host-key name (HT.bindings sample-table)
same-table = signature-immutable-real zero (suc zero) sample-table sample-table refl

-- NEGATIVE CONTROL: two DIFFERENT tables. The conclusion is not
-- available, so the hypothesis cannot be dropped.
other-table : HostTable Name
other-table = record { bindings = extract-names ("Boundary#Box" ∷ []) ; aliases = [] }

different-tables-need-not-agree :
  ¬ (∀ name → HT.host-key name (HT.bindings sample-table)
            ≡ HT.host-key name (HT.bindings other-table))
different-tables-need-not-agree h with h "Boundary#Packed"
... | ()

------------------------------------------------------------------------
-- The old, vacuous statement holds for an ARBITRARY function -- which
-- is precisely why it proved nothing. Recorded as a control so the
-- replacement is not mistaken for a restatement.
------------------------------------------------------------------------

vacuous-holds-for-anything : ∀ (f : ℕ → Name → Maybe Name) (stage : ℕ) name
  → f stage name ≡ f stage name
vacuous-holds-for-anything = signature-immutable-vacuous

------------------------------------------------------------------------
-- The ledger, instantiated: four discharged, four remaining.
------------------------------------------------------------------------

m2b-split : length (discharged m2b-ledger) ≡ 4 × length (remaining m2b-ledger) ≡ 4
m2b-split = refl , refl
