%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

g : N -> N
g Z = Z
g (S k) = S k

toS : (m : N) -> SN m
toS Z = SZ
toS (S j) = SS (toS j)

foo : (n : N) -> SN (g n)
foo n with (g n)
  foo n | Z = SZ
  foo n | (S k) = SS (toS k)
