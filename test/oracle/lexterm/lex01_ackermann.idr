%default total

data Nat2 = Z | S Nat2

ack : Nat2 -> Nat2 -> Nat2
ack Z n = S n
ack (S m) Z = ack m (S Z)
ack (S m) (S n) = ack m (ack (S m) n)
