%default total

data N = Z | S N

f : N -> N
f n = case n of
        S (S m) => m
        Z => Z
