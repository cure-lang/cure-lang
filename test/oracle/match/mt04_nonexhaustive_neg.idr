%default total

data N = Z | S N

combine : N -> N -> N
combine Z m = m
combine (S k) m = case m of
  Z => k
