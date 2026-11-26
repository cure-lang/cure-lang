module RejectLimitFinite where

open import Agda.Primitive using (Level; Setω)

bad : (a : Level) → Set a
bad a = Setω
