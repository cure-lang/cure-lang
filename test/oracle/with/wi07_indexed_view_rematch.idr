%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

data NV : N -> Type where
  VZ : NV Z
  VS : {n : N} -> SN n -> NV (S n)

toS : (m : N) -> SN m
toS Z = SZ
toS (S j) = SS (toS j)

view : (n : N) -> NV n
view Z = VZ
view (S m) = VS (toS m)

foo : (n : N) -> SN n -> SN n
foo n w with (view n)
  foo Z w | VZ = w
  foo (S m) w | (VS s) = w
