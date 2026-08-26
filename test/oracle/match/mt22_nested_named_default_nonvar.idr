%default total

data N = Z | S N

f : N -> N
f n = case S n of
        S Z => Z
        other => other
