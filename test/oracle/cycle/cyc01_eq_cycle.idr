%default total

data Nat2 = Z | S Nat2

data MyEq : a -> a -> Type where
  MRefl : MyEq w w

noCycle : {n : Nat2} -> MyEq n (S n) -> Nat2
noCycle MRefl impossible
