%default total

data N = Z | S N

ap : (N -> N) -> N -> N
ap f x = f x

inc : N -> N
inc n = S n

g : N
g = ap inc (S Z)
