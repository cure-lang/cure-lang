%default total

data Nat' = Z | S Nat'

two : Nat'
two = S (S Z)

pred' : Nat' -> Nat'
pred' Z = Z
pred' (S m) = m
