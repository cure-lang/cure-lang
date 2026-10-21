------------------------------------------------------------------------
-- Structural syntax equality, NOT conversion or an external decoder.
-- The auxiliary code retraction avoids unchecked constructor reflection.
-- Malformed codes may decode to defaults; only encode/decode identity is
-- used to derive equality of actual Terms. No wire parser is supplied.
------------------------------------------------------------------------
module Core.SyntaxEquality where

open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
import Data.String.Properties as String
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Core.Syntax
open import Core.Grade using (Grade; erased; linear; affine; unrestricted)
open import Core.Universe using (Level; l0; l1; l2; toNat)

data Code : Set where
  node : ℕ → Name → ℕ → List Code → Code

grade-number : Grade → ℕ
grade-number erased = 0
grade-number linear = 1
grade-number affine = 2
grade-number unrestricted = 3
number-grade : ℕ → Grade
number-grade 0 = erased
number-grade 1 = linear
number-grade 2 = affine
number-grade _ = unrestricted
grade-roundtrip : ∀ g → number-grade (grade-number g) ≡ g
grade-roundtrip erased = refl
grade-roundtrip linear = refl
grade-roundtrip affine = refl
grade-roundtrip unrestricted = refl
number-level : ℕ → Level
number-level 0 = l0
number-level 1 = l1
number-level _ = l2
level-roundtrip : ∀ l → number-level (toNat l) ≡ l
level-roundtrip l0 = refl
level-roundtrip l1 = refl
level-roundtrip l2 = refl

mutual
  encode : Term → Code
  encode (tm-type l) = node 0 "" (toNat l) []
  encode (tm-var k) = node 1 "" k []
  encode (tm-pi g d c) = node 2 "" (grade-number g) (encode d ∷ encode c ∷ [])
  encode (tm-lam g d b) = node 3 "" (grade-number g) (encode d ∷ encode b ∷ [])
  encode (tm-let g ty v b) = node 4 "" (grade-number g) (encode ty ∷ encode v ∷ encode b ∷ [])
  encode (tm-app f a) = node 5 "" 0 (encode f ∷ encode a ∷ [])
  encode (tm-data name ps is) =
    node 6 name 0 (node 100 "" 0 (encodeTerms ps) ∷ node 100 "" 0 (encodeTerms is) ∷ [])
  encode (tm-ctor name args) = node 7 name 0 (encodeTerms args)
  encode (tm-case s m bs) =
    node 8 "" 0 (encode s ∷ encode m ∷ node 100 "" 0 (encodeBranches bs) ∷ [])
  encode (tm-global name) = node 9 name 0 []
  encode tm-int_type = node 10 "" 0 []
  encode (tm-int_lit (pos n)) = node 11 "" n []
  encode (tm-int_lit (negsuc n)) = node 12 "" n []
  encode (tm-nat_lit n) = node 13 "" n []
  encode (tm-bounded_lit n) = node 14 "" n []
  encode tm-float_type = node 15 "" 0 []
  encode tm-float_lit = node 16 "" 0 []
  encode tm-binary_type = node 17 "" 0 []
  encode tm-atom_type = node 18 "" 0 []
  encode (tm-atom_lit name) = node 19 name 0 []
  encode (tm-effect_type t) = node 20 "" 0 (encode t ∷ [])
  encode (tm-effect_pure t) = node 20 "" 1 (encode t ∷ [])
  encode (tm-effect_bind e k) = node 20 "" 2 (encode e ∷ encode k ∷ [])
  encode (tm-hole name) = node 20 name 3 []
  encode tm-absurd = node 20 "" 4 []

  encodeTerms : List Term → List Code
  encodeTerms [] = []
  encodeTerms (t ∷ ts) = encode t ∷ encodeTerms ts
  encodeBranch : Branch → Code
  encodeBranch (name , arity , body) = node 0 name arity (encode body ∷ [])
  encodeBranches : List Branch → List Code
  encodeBranches [] = []
  encodeBranches (b ∷ bs) = encodeBranch b ∷ encodeBranches bs

mutual
  decode : Code → Term
  decode (node 0 name level children) = tm-type (number-level level)
  decode (node 1 name index children) = tm-var index
  decode (node 2 name grade (d ∷ c ∷ [])) = tm-pi (number-grade grade) (decode d) (decode c)
  decode (node 3 name grade (d ∷ b ∷ [])) = tm-lam (number-grade grade) (decode d) (decode b)
  decode (node 4 name grade (ty ∷ v ∷ b ∷ [])) =
    tm-let (number-grade grade) (decode ty) (decode v) (decode b)
  decode (node 5 name number (f ∷ a ∷ [])) = tm-app (decode f) (decode a)
  decode (node 6 name number (node _ _ _ ps ∷ node _ _ _ is ∷ [])) =
    tm-data name (decodeTerms ps) (decodeTerms is)
  decode (node 7 name number args) = tm-ctor name (decodeTerms args)
  decode (node 8 name number (s ∷ m ∷ node _ _ _ bs ∷ [])) =
    tm-case (decode s) (decode m) (decodeBranches bs)
  decode (node 9 name number children) = tm-global name
  decode (node 10 name number children) = tm-int_type
  decode (node 11 name number children) = tm-int_lit (pos number)
  decode (node 12 name number children) = tm-int_lit (negsuc number)
  decode (node 13 name number children) = tm-nat_lit number
  decode (node 14 name number children) = tm-bounded_lit number
  decode (node 15 name number children) = tm-float_type
  decode (node 16 name number children) = tm-float_lit
  decode (node 17 name number children) = tm-binary_type
  decode (node 18 name number children) = tm-atom_type
  decode (node 19 name number children) = tm-atom_lit name
  decode (node 20 name 0 (t ∷ [])) = tm-effect_type (decode t)
  decode (node 20 name 1 (t ∷ [])) = tm-effect_pure (decode t)
  decode (node 20 name 2 (e ∷ k ∷ [])) = tm-effect_bind (decode e) (decode k)
  decode (node 20 name 3 children) = tm-hole name
  decode (node 20 name 4 children) = tm-absurd
  decode _ = tm-absurd

  decodeTerms : List Code → List Term
  decodeTerms [] = []
  decodeTerms (t ∷ ts) = decode t ∷ decodeTerms ts
  decodeBranch : Code → Branch
  decodeBranch (node 0 name arity (body ∷ [])) = name , arity , decode body
  decodeBranch _ = "" , 0 , tm-absurd
  decodeBranches : List Code → List Branch
  decodeBranches [] = []
  decodeBranches (b ∷ bs) = decodeBranch b ∷ decodeBranches bs


mutual
  roundtrip : ∀ t → decode (encode t) ≡ t
  roundtrip (tm-type l) = cong tm-type (level-roundtrip l)
  roundtrip (tm-var k) = refl
  roundtrip (tm-pi g d c) rewrite grade-roundtrip g = cong₂ (tm-pi g) (roundtrip d) (roundtrip c)
  roundtrip (tm-lam g d b) rewrite grade-roundtrip g = cong₂ (tm-lam g) (roundtrip d) (roundtrip b)
  roundtrip (tm-let g ty v b) rewrite grade-roundtrip g =
    cong₃ (tm-let g) (roundtrip ty) (roundtrip v) (roundtrip b)
  roundtrip (tm-app f a) = cong₂ tm-app (roundtrip f) (roundtrip a)
  roundtrip (tm-data name ps is) = cong₂ (tm-data name) (terms-roundtrip ps) (terms-roundtrip is)
  roundtrip (tm-ctor name args) = cong (tm-ctor name) (terms-roundtrip args)
  roundtrip (tm-case s m bs) = cong₃ tm-case (roundtrip s) (roundtrip m) (branches-roundtrip bs)
  roundtrip (tm-global name) = refl
  roundtrip tm-int_type = refl
  roundtrip (tm-int_lit (pos n)) = refl
  roundtrip (tm-int_lit (negsuc n)) = refl
  roundtrip (tm-nat_lit n) = refl
  roundtrip (tm-bounded_lit n) = refl
  roundtrip tm-float_type = refl
  roundtrip tm-float_lit = refl
  roundtrip tm-binary_type = refl
  roundtrip tm-atom_type = refl
  roundtrip (tm-atom_lit name) = refl
  roundtrip (tm-effect_type t) = cong tm-effect_type (roundtrip t)
  roundtrip (tm-effect_pure t) = cong tm-effect_pure (roundtrip t)
  roundtrip (tm-effect_bind e k) = cong₂ tm-effect_bind (roundtrip e) (roundtrip k)
  roundtrip (tm-hole name) = refl
  roundtrip tm-absurd = refl

  terms-roundtrip : ∀ ts → decodeTerms (encodeTerms ts) ≡ ts
  terms-roundtrip [] = refl
  terms-roundtrip (t ∷ ts) = cong₂ _∷_ (roundtrip t) (terms-roundtrip ts)
  branch-roundtrip : ∀ b → decodeBranch (encodeBranch b) ≡ b
  branch-roundtrip (name , arity , body) = cong (λ b → name , arity , b) (roundtrip body)
  branches-roundtrip : ∀ bs → decodeBranches (encodeBranches bs) ≡ bs
  branches-roundtrip [] = refl
  branches-roundtrip (b ∷ bs) = cong₂ _∷_ (branch-roundtrip b) (branches-roundtrip bs)

mutual
  code-equal? : (a b : Code) → Dec (a ≡ b)
  code-equal? (node tag name number children) (node other label value arguments) with Nat._≟_ tag other
  ... | no unequal = no (λ { refl → unequal refl })
  ... | yes refl with String._≟_ name label
  ... | no unequal = no (λ { refl → unequal refl })
  ... | yes refl with Nat._≟_ number value
  ... | no unequal = no (λ { refl → unequal refl })
  ... | yes refl with codes-equal? children arguments
  ... | no unequal = no (λ { refl → unequal refl })
  ... | yes refl = yes refl

  codes-equal? : (xs ys : List Code) → Dec (xs ≡ ys)
  codes-equal? [] [] = yes refl
  codes-equal? [] (_ ∷ _) = no (λ ())
  codes-equal? (_ ∷ _) [] = no (λ ())
  codes-equal? (x ∷ xs) (y ∷ ys) with code-equal? x y
  ... | no unequal = no (λ { refl → unequal refl })
  ... | yes refl with codes-equal? xs ys
  ... | no unequal = no (λ { refl → unequal refl })
  ... | yes refl = yes refl

equal? : (t u : Term) → Dec (t ≡ u)
equal? t u with code-equal? (encode t) (encode u)
... | no unequal = no (λ same → unequal (cong encode same))
... | yes same = yes (trans (sym (roundtrip t)) (trans (cong decode same) (roundtrip u)))
