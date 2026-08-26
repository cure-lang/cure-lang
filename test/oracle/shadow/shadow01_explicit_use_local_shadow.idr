%default total

data Nat' = Zero | Suc Nat'

add : Nat' -> Nat' -> Nat'
add Zero b = b
add (Suc m) b = Suc (add m b)
