%default total

data Nat2 = Z2 | S2 Nat2

data Vec : Type -> Nat2 -> Type where
  VNil : Vec a Z2
  VCons : a -> Vec a n -> Vec a (S2 n)

f : {0 a : Type} -> {0 k : Nat2} -> Vec a (S2 k) -> Vec a (S2 k)
f v@(VCons {n = k} h t) = v
