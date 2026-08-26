%default total

data Nat2 = Zero | Suc Nat2

data Vect : Type -> Nat2 -> Type where
  Empty : Vect a Zero
  Prepend : a -> Vect a n -> Vect a (Suc n)

second : {a : Type} -> {k : Nat2} -> Vect a (Suc (Suc k)) -> a
second (Prepend x (Prepend y r)) = y
