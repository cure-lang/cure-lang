%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

record Box a where
  constructor MkBox
  item : a
  tag : N
  pf : SN tag

mk : Box N
mk = MkBox Z (S Z) (SS SZ)

getTag : Box N -> N
getTag b = b.tag
