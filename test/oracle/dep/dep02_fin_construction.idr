%default total

data Nat2 = Zero | Suc Nat2

data Fin2 : Nat2 -> Type where
  FZ : Fin2 (Suc m)
  FS : Fin2 m -> Fin2 (Suc m)

f1 : Fin2 (Suc (Suc Zero))
f1 = FS FZ
