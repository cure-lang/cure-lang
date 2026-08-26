%default total

data Nat2 = Z | S Nat2

plus : Nat2 -> Nat2 -> Nat2
plus Z n = n
plus (S k) n = S (plus k n)

data Vec : Nat2 -> Type where
  VZ : Vec Z
  VS : Vec k -> Vec (S k)

stuck : {m : Nat2} -> Vec (plus m Z) -> Nat2 -> Nat2
stuck _ r = r

use : Nat2
use = stuck (VS VZ) Z
