%default total
data Nat2 = Z | S Nat2
data MyEq : a -> a -> Type where
  MRefl : MyEq w w
noCycle2 : {n : Nat2} -> MyEq n (S (S n)) -> Nat2
noCycle2 MRefl impossible
