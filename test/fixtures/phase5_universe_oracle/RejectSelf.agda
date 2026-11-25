module RejectSelf where

open import Agda.Primitive using (Level)

bad : (a : Level) → Set a
bad a = Set a
