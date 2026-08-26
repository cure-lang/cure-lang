%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

data NVv : N -> Type where
  VZ : NVv Z
  VC : (k : N) -> SN k -> NVv (S k)

pred : (n : N) -> NVv n -> N
pred n v with (v)
  pred _ v | VZ = Z
  pred _ v | (VC k s) = k
