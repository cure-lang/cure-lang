%default total

data Nat' = Z | S Nat'
data Bool' = T | F
data Lst a = Nil | Cons a (Lst a)

g : Lst Nat'
g = Cons T Nil
