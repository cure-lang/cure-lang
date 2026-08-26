%default total

data Nat2 = Zero | Suc Nat2

data MyList a = LNil | LCons a (MyList a)

firstOr : a -> MyList a -> a
firstOr d (LCons x xs) = x
firstOr d LNil = d

g : Nat2
g = firstOr Zero (LCons (Suc Zero) LNil)
