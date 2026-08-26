%default total

data Nat' = Zero | Suc Nat'

data Vector : Type -> Nat' -> Type where
  Empty : Vector a Zero
  Prepend : a -> Vector a n -> Vector a (Suc n)

data Fin' : Nat' -> Type where
  FZ : Fin' (Suc m)
  FS : Fin' m -> Fin' (Suc m)

lookup' : Vector a n -> Fin' n -> a
lookup' Empty i = case i of {}
lookup' (Prepend x xs) FZ = x
lookup' (Prepend x xs) (FS j) = lookup' xs j

vec : Vector Nat' (Suc (Suc Zero))
vec = Prepend (Suc Zero) (Prepend Zero Empty)

at1 : Nat'
at1 = lookup' vec (FS FZ)
