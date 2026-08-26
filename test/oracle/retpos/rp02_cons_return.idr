%default total

data Nat' = Z | S Nat'
data Lst a = Nil | Cons a (Lst a)

g : Lst Nat'
g = Cons Z Nil
