%default total

data N = Zero | Suc N

mutual
  calleeFirst : N -> N
  calleeFirst n = helper n

  helper : N -> N
  helper n = Suc n

g : N
g = calleeFirst Zero
