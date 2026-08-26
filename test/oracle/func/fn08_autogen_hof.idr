%default total

data N = Zero | Suc N

ap : (a -> b) -> a -> b
ap f x = f x

inc : N -> N
inc n = Suc n

g : N
g = ap inc (Suc Zero)
