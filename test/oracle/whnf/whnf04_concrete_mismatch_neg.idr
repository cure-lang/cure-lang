%default total

data Nat2 = Z | S Nat2

plus : Nat2 -> Nat2 -> Nat2
plus Z n = n
plus (S k) n = S (plus k n)

data Vec : Nat2 -> Type where
  VZ : Vec Z
  VS : Vec k -> Vec (S k)

wants : Vec (plus Z (S Z)) -> Nat2
wants _ = Z

use : Nat2
use = wants VZ
