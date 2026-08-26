%default total

data Nat2 = Z | S Nat2

f : Nat2 -> Nat2 -> Nat2
f Z b = b
f (S x) Z = f x x
f (S x) (S y) = f y x
