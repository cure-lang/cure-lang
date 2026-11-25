module RejectDescending where

open import Agda.Primitive using (Level; lsuc)

bad : {a : Level} → Set (lsuc a) → Set a
bad A = A
