module MaximumLaws where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

data Equal {a : Level} (A : Set a) (x : A) : A → Set a where
  same : Equal A x x

commutative : (a b : Level) → Equal Level (a ⊔ b) (b ⊔ a)
commutative a b = same

associative : (a b c : Level) → Equal Level ((a ⊔ b) ⊔ c) (a ⊔ (b ⊔ c))
associative a b c = same

idempotent : (a : Level) → Equal Level (a ⊔ a) a
idempotent a = same

zero-neutral : (a : Level) → Equal Level (a ⊔ lzero) a
zero-neutral a = same

successor-distributes : (a b : Level) → Equal Level (lsuc (a ⊔ b)) (lsuc a ⊔ lsuc b)
successor-distributes a b = same

absorbs-predecessor : (a : Level) → Equal Level (a ⊔ lsuc a) (lsuc a)
absorbs-predecessor a = same
