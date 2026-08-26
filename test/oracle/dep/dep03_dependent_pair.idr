%default total

data Nat2 = Zero | Suc Nat2

data Vect : Type -> Nat2 -> Type where
  Empty : Vect a Zero
  Prepend : a -> Vect a n -> Vect a (Suc n)

twoVec : (n : Nat2 ** Vect Nat2 n)
twoVec = (Suc (Suc Zero) ** Prepend Zero (Prepend (Suc Zero) Empty))

theLen : Nat2
theLen = fst twoVec
