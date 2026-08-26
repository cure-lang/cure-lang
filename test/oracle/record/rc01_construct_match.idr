%default total

data N = Z | S N

record Point where
  constructor MkPoint
  x : N
  y : N

getx : Point -> N
getx p = case p of
           MkPoint a b => a

g : N
g = getx (MkPoint (S Z) Z)
