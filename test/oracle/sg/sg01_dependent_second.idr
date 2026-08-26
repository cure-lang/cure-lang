%default total

data MySigma : (a : Type) -> (b : a -> Type) -> Type where
  MkPair : (x : a) -> b x -> MySigma a b

first : MySigma a b -> a
first (MkPair x y) = x

second : (p : MySigma a b) -> b (first p)
second (MkPair x y) = y
