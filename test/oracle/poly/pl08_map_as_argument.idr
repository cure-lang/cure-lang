%default total

data Nat2 = Zero | Suc Nat2

data MyList a = LNil | LCons a (MyList a)

mapL : (a -> b) -> MyList a -> MyList b
mapL f LNil = LNil
mapL f (LCons x xs) = LCons (f x) (mapL f xs)

s : Nat2 -> Nat2
s n = Suc n

mklist : MyList Nat2
mklist = LCons Zero (LCons (Suc Zero) LNil)

hd : Nat2 -> MyList Nat2 -> Nat2
hd d LNil = d
hd d (LCons x xs) = x

g : Nat2
g = hd Zero (mapL s mklist)
