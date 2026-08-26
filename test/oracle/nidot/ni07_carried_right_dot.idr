%default total

data Nat2 = Z2 | S2 Nat2

data H : Nat2 -> Nat2 -> Type where
  HMk : {0 m : Nat2} -> H (S2 m) m

f : {0 j : Nat2} -> H (S2 j) j -> Nat2
f (HMk {m = j}) = Z2
