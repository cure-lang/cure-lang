%default total

data Nat2 = Z | S Nat2

count_down : Nat2 -> Nat2 -> Nat2
count_down acc Z = acc
count_down acc (S m) = count_down (S acc) m
