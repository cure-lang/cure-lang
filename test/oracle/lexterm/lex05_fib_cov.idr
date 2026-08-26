%default total

data Nat2 = Z | S Nat2

add : Nat2 -> Nat2 -> Nat2
add Z b = b
add (S m) b = S (add m b)

fib : Nat2 -> Nat2
fib Z = Z
fib (S Z) = S Z
fib (S (S j)) = add (fib (S j)) (fib j)
