%default total

data N = Z | S N

ap : (N -> N) -> N -> N
ap f x = f x

g : N -> N
g n = ap (\y => S y) n
