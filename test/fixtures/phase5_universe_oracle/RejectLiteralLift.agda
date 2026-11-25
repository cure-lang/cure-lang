module RejectLiteralLift where

open import Agda.Primitive using (Level; _⊔_)

bad : (a b : Level) → Set (a ⊔ b)
bad a b = Set a
