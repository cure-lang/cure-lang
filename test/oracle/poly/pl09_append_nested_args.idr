%default total

data Nat2 = Zero | Suc Nat2

data MyList a = LNil | LCons a (MyList a)

app : MyList a -> MyList a -> MyList a
app LNil ys = ys
app (LCons x r) ys = LCons x (app r ys)

hd : Nat2 -> MyList Nat2 -> Nat2
hd d LNil = d
hd d (LCons x xs) = x

g : Nat2
g = hd Zero (app (LCons (Suc Zero) LNil) (LCons Zero LNil))
