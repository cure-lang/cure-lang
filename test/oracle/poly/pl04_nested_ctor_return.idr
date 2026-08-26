%default total

data Nat2 = Zero | Suc Nat2

data MyList a = LNil | LCons a (MyList a)

one : MyList Nat2
one = LCons Zero LNil

hd : Nat2 -> MyList Nat2 -> Nat2
hd d (LCons x xs) = x
hd d LNil = d

g : Nat2
g = hd (Suc Zero) one
