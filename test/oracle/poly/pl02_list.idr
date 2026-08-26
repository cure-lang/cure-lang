%default total

data N = Z | S N

data Lst a = Nil | Cons a (Lst a)

hd : N -> Lst N -> N
hd d l = case l of
           Cons x xs => x
           Nil => d

g : N
g = hd Z (Cons (S Z) Nil)
