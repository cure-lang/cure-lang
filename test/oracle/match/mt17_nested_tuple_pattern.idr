%default total

data N = Z | S N

f : (N, (N, N)) -> N
f p = case p of
        (x, (y, z)) => z

g : N
g = f (Z, (S Z, S (S Z)))
