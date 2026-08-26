%default total

data N = Zero | Suc N

myconst : a -> b -> a
myconst x y = x

g : N
g = myconst (Suc Zero) Zero
