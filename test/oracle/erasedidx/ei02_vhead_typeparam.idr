%default total

data Nat' = Z | S Nat'

data Vector : Type -> Nat' -> Type where
  Empty : Vector a Z
  Prepend : a -> Vector a n -> Vector a (S n)

vhead : {a : Type} -> {n : Nat'} -> Vector a (S n) -> a
vhead (Prepend x xs) = x

one : Nat'
one = vhead (Prepend (S Z) Empty)
