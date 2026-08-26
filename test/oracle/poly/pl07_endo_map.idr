%default total

data Nat2 = Zero | Suc Nat2

data MyList a = LNil | LCons a (MyList a)

emap : (a -> a) -> MyList a -> MyList a
emap f LNil = LNil
emap f (LCons x xs) = LCons (f x) (emap f xs)

s : Nat2 -> Nat2
s n = Suc n

mklist : MyList Nat2
mklist = LCons Zero (LCons (Suc Zero) LNil)

g : MyList Nat2
g = emap s mklist
