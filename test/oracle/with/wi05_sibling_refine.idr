%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

g : N -> N
g Z = Z
g (S k) = S k

consume : (m : N) -> SN m -> N
consume m s = m

foo : (n : N) -> SN (g n) -> N
foo n pf with (g n)
  foo n pf | Z = consume Z pf
  foo n pf | (S k) = consume (S k) pf
