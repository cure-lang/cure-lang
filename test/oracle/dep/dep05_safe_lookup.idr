%default total

data Nat2 = Zero | Suc Nat2

data Vect : Type -> Nat2 -> Type where
  Empty : Vect a Zero
  Prepend : a -> Vect a n -> Vect a (Suc n)

data Fin2 : Nat2 -> Type where
  FZ : Fin2 (Suc m)
  FS : Fin2 m -> Fin2 (Suc m)

lookup2 : Vect a n -> Fin2 n -> a
lookup2 (Prepend x xs) FZ = x
lookup2 (Prepend x xs) (FS j) = lookup2 xs j

vec : Vect Nat2 (Suc (Suc Zero))
vec = Prepend (Suc Zero) (Prepend Zero Empty)

at0 : Nat2
at0 = lookup2 vec FZ

at1 : Nat2
at1 = lookup2 vec (FS FZ)
