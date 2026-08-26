%default total

data Nat2 = Z | S Nat2
data Bool2 = True2 | False2

is_even : Nat2 -> Bool2
is_odd : Nat2 -> Bool2
is_even Z = True2
is_even (S m) = is_odd m
is_odd Z = False2
is_odd (S m) = is_even m
