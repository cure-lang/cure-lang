%default total

data Nat' = Z | S Nat'

data Vec : Nat' -> Type where
  VNil : Vec Z
  VCons : Nat' -> Vec k -> Vec (S k)

vhead : {n : Nat'} -> Vec (S n) -> Nat'
vhead (VCons h r) = h

one : Nat'
one = vhead (VCons (S Z) VNil)
