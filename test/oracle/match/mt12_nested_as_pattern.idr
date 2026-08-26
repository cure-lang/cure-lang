%default total

data N = Z | S N
data L = Nil | Cons N L

f : L -> L
f xs = case xs of
         Cons h (t@(Cons y r)) => t
         Cons h r => r
         Nil => Nil
