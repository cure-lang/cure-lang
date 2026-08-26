%default total

data N = Z | S N

f : (N, N) -> N
f p = case p of
        _ => Z

g : N
g = f (S Z, Z)
