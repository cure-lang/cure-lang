%default total

data N = Z | S N

Endo : Type
Endo = N -> N

ap : Endo -> N -> N
ap f x = f x

inc : N -> N
inc n = S n

g : N
g = ap inc Z
