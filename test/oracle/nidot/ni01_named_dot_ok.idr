%default total

data Nat2 = Z | S Nat2

data Vec : Nat2 -> Type where
  VNil : Vec Z
  VCons : Nat2 -> Vec k -> Vec (S k)

vhead : {m : Nat2} -> Vec (S m) -> Nat2
vhead (VCons {k = m} h r) = h
