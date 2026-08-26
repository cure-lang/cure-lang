%default total

data N = Z | S N

f : N -> N
f n =
  case (case n of { S m => m; other => Z }) of
    Z => Z
    k => S k
