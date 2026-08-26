%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

g : N -> N
g Z = Z
g (S k) = S k

foo : (n : N) -> SN (g n)
foo n with (g n)
  foo n | Z = SZ
