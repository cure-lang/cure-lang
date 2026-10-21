------------------------------------------------------------------------
-- Finite reflexive-transitive closure and the STRONG diamond argument.
-- Local joinability alone is deliberately not an input to this theorem.
------------------------------------------------------------------------
{-# OPTIONS --safe #-}
module Core.Relation where

open import Data.Product using (∃; _×_; _,_)

data Star {A : Set} (R : A → A → Set) : A → A → Set where
  done : ∀ {x} → Star R x x
  step : ∀ {x y z} → R x y → Star R y z → Star R x z

append : ∀ {A : Set} {R : A → A → Set} {x y z}
  → Star R x y → Star R y z → Star R x z
append done q = q
append (step p ps) q = step p (append ps q)

map-star : ∀ {A B : Set} {R : A → A → Set} {S : B → B → Set}
  → (f : A → B) → (∀ {x y} → R x y → S (f x) (f y))
  → ∀ {x y} → Star R x y → Star S (f x) (f y)
map-star f lift done = done
map-star f lift (step p ps) = step (lift p) (map-star f lift ps)

Diamond : ∀ {A : Set} → (A → A → Set) → Set
Diamond R = ∀ {t u v} → R t u → R t v → ∃ λ w → R u w × R v w

module Closure {A : Set} (R : A → A → Set) (diamond : Diamond R) where
  -- Induction only on the input path, never a generated joining path.
  strip : ∀ {t u v} → R t u → Star R t v
    → ∃ λ w → Star R u w × R v w
  strip p done = _ , done , p
  strip p (step q qs) with diamond p q
  ... | w , uw , vw with strip vw qs
  ... | z , wz , vz = z , step uw wz , vz

  confluent : ∀ {t u v} → Star R t u → Star R t v
    → ∃ λ w → Star R u w × Star R v w
  confluent done q = _ , q , done
  confluent (step p ps) q with strip p q
  ... | w , uw , vw with confluent ps uw
  ... | z , uz , wz = z , uz , step vw wz
