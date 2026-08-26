%default total

data N = Z | S N

f : N -> N
f n = case S n of
        Z => Z
        other => other
