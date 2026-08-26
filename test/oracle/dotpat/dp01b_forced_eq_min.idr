%default total

data Nat2 = Z | S Nat2

data SameLen : Nat2 -> Nat2 -> Type where
  Same : SameLen k k

cong : {a : Nat2} -> {b : Nat2} -> SameLen a b -> SameLen (S a) (S b)
cong Same = Same
