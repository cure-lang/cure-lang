%default total

data N = Zero | Suc N

myid : a -> a
myid x = x

g : N
g = myid (Suc Zero)
