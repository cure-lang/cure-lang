%default total

data N = Z | S N

MyN : Type
MyN = N

f : MyN -> MyN
f n = S n

g : N
g = f (S Z)
