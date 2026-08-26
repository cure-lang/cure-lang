%default total

data Nat' = Zero | Suc Nat'

data Vector : Type -> Nat' -> Type where
  Empty : Vector a Zero
  Prepend : a -> Vector a n -> Vector a (Suc n)

single : {a : Type} -> a -> (n : Nat' ** Vector a n)
single x = (Suc (Suc Zero) ** Prepend x Empty)
