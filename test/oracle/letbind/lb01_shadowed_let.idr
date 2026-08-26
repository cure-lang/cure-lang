%default total

data N = Z | S N
data Op = A N | B N

f : N -> Op -> N
f n o = let x = S n in case o of
  A x => x
  B y => x
