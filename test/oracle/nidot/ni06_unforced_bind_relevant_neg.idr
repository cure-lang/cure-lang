%default total

data Nat2 = Z2 | S2 Nat2

data Vec : Nat2 -> Type where
  VNil : Vec Z2
  VCons : Nat2 -> Vec n -> Vec (S2 n)

data P : Type where
  MkP : {0 k : Nat2} -> Vec k -> P

f : P -> Nat2
f (MkP {k = kk} v) = kk
