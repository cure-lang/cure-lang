module RejectDependentFinite where

open import Agda.Primitive using (Level)

bad : (a : Level) → Set a
bad a = (b : Level) → Set b
