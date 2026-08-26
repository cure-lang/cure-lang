%default total

data N = Z | S N

myid : a -> a
myid x = x

g : N
g = myid (S Z)
