module Cumulativity where

open import Agda.Primitive using (Level; lsuc; _⊔_)

lift-carrier : {a b : Level} → Set a → Set (a ⊔ b)
lift-carrier A = A

lift-value : {a b : Level} → (A : Set a) → A → lift-carrier {a} {b} A
lift-value A x = x

literal-lift : (a b : Level) → Set (lsuc a ⊔ b)
literal-lift a b = Set a
