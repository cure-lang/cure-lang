%default total

data Nat2 = Zero | Suc Nat2

data Vect : Type -> Nat2 -> Type where
  Empty : Vect a Zero
  Prepend : a -> Vect a n -> Vect a (Suc n)

add : Nat2 -> Nat2 -> Nat2
add Zero y = y
add (Suc p) y = Suc (add p y)

zipAdd : {n : Nat2} -> Vect Nat2 n -> Vect Nat2 n -> Vect Nat2 n
zipAdd xs ys = case (xs, ys) of
                 (Empty, Empty) => Empty
                 (Prepend x xr, Prepend y yr) => Prepend (add x y) (zipAdd xr yr)
