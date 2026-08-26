%default total

data Nat2 = Zero | Suc Nat2

data Vect : Type -> Nat2 -> Type where
  Empty : Vect a Zero
  Prepend : a -> Vect a n -> Vect a (Suc n)

data Fin2 : Nat2 -> Type where
  FZ : Fin2 (Suc m)
  FS : Fin2 m -> Fin2 (Suc m)

lookup2 : Fin2 n -> Vect a n -> a
lookup2 FZ (Prepend x xs) = x
lookup2 (FS j) (Prepend x xs) = lookup2 j xs

vec : Vect Nat2 (Suc (Suc Zero))
vec = Prepend (Suc Zero) (Prepend Zero Empty)

at0 : Nat2
at0 = lookup2 FZ vec

at1 : Nat2
at1 = lookup2 (FS FZ) vec
