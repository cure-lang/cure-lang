module Formation where

open import Agda.Primitive using (Level; lsuc)

universe : (a : Level) → Set (lsuc a)
universe a = Set a

closed-universe : Set₃₈
closed-universe = Set₃₇

identity : {a : Level} {A : Set a} → A → A
identity x = x
