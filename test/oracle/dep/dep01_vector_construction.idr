%default total

data Nat2 = Zero | Suc Nat2

data Vect : Type -> Nat2 -> Type where
  Empty : Vect a Zero
  Prepend : a -> Vect a n -> Vect a (Suc n)

v2 : Vect Nat2 (Suc (Suc Zero))
v2 = Prepend Zero (Prepend (Suc Zero) Empty)
