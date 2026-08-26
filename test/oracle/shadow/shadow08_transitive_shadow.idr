%default total

data Nat' = Zero | Suc Nat'

two : Nat'
two = Suc (Suc Zero)

pred' : Nat' -> Nat'
pred' Zero = Zero
pred' (Suc m) = m
