%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

data Two : N -> N -> Type where
  MkTwo : {x, y : N} -> SN x -> SN y -> Two x y

toS : (m : N) -> SN m
toS Z = SZ
toS (S j) = SS (toS j)

g : N -> N
g Z = Z
g (S k) = S k

foo : (a, b : N) -> Two (g a) (g b)
foo a b with (g a)
  foo a b | Z with (g b)
    foo a b | Z | Z = MkTwo SZ SZ
    foo a b | Z | (S k) = MkTwo SZ (SS (toS k))
  foo a b | (S j) with (g b)
    foo a b | (S j) | Z = MkTwo (SS (toS j)) SZ
    foo a b | (S j) | (S k) = MkTwo (SS (toS j)) (SS (toS k))
