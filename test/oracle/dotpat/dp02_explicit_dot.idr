%default total

data Nat2 = Z | S Nat2

data MyEq : a -> a -> Type where
  MRefl : MyEq w w

congS : {a : Nat2} -> {b : Nat2} -> MyEq a b -> MyEq (S a) (S b)
congS (MRefl {w = a}) = MRefl
