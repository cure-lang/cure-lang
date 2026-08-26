%default total

data N = Z | S N

record Point where
  constructor MkPoint
  x : N
  y : N

bump : Point -> Point
bump p = { x := S Z } p

g : N
g = x (bump (MkPoint Z (S (S Z))))
