%default total

data Nat2 = Z | S Nat2

plus : Nat2 -> Nat2 -> Nat2
plus Z n = n
plus (S k) n = S (plus k n)

data Vec : Nat2 -> Type where
  VZ : Vec Z
  VS : Vec k -> Vec (S k)

needlen : {m : Nat2} -> Vec (plus Z m) -> Nat2 -> Nat2
needlen _ r = r

use : Nat2
use = needlen (VS VZ) Z
