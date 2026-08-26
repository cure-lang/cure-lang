%default total

data Local = Zero | Suc Local

importedTwo : Nat
importedTwo = S (S Z)

isZero : Nat -> Local
isZero Z = Zero
isZero (S k) = Suc Zero
