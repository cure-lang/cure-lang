module RejectUnrelated where

open import Agda.Primitive using (Level)

bad : {a b : Level} → Set a → Set b
bad A = A
