%default total

data N = Z | S N

record Box a where
  constructor MkBox
  val : a

unbox : Box N -> N
unbox b = val b

g : N
g = unbox (MkBox (S Z))
