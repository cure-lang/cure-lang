%default total

data N = Z | S N

data T = A (N, N) | B

f : T -> N
f t = case t of
        A (x, y) => y
        B => Z

g : N
g = f (A (Z, S Z))
