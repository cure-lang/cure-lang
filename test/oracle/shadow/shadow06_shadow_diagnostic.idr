%default total

data Nat' = Zero | Suc Nat'

bad : Nat' -> Nat'
bad Z = Zero
bad (S m) = Suc m
