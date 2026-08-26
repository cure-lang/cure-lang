%default total

data Local = Zero | Suc Local

isZero : Nat -> Local
isZero Z = Zero
isZero (S k) = Suc Zero
