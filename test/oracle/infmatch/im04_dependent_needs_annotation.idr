%default total

data N = Zero | Suc N
data Vector : Type -> N -> Type where
  Empty : Vector a Zero
  Prepend : a -> Vector a n -> Vector a (Suc n)

foo : (m : N) -> Vector N m -> N
foo m v =
  let b = case v of
            Prepend x rest => rest
            Empty => Empty
  in case b of
       Empty => Zero
       Prepend y ys => Zero
