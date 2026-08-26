%default total

data N = Z | S N

id2 : N -> N
id2 n = n

f : N -> N
f n = case id2 n of
  Z => S Z
  other => other
