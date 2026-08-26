%default total

data N = Z | S N

f : N -> N
f n = case n of
        w@(S m) => w
        Z => Z
