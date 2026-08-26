%default total

data N = Z | S N

f : (N, N) -> N
f p = case p of
        (x, y) => y

g : N
g = f (Z, S Z)
