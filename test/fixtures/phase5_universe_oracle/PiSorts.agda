module PiSorts where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)

finite-pi : (a b : Level) → Set (lsuc a ⊔ lsuc b)
finite-pi a b = (A : Set a) → Set b

dependent-pi : Setω
dependent-pi = (a : Level) → Set a

limit-formation : Setω₁
limit-formation = Setω

limit-lift : Setω₁
limit-lift = (a : Level) → Set a
