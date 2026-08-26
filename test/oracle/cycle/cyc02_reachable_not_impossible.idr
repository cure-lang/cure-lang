%default total
data Nat2 = Z | S Nat2
data MyEq : a -> a -> Type where
  MRefl : MyEq w w
bad : {n : Nat2} -> MyEq n n -> Nat2
bad MRefl impossible
