%default total

data N = Z | S N

cong' : {0 a : Type} -> {0 x : a} -> {0 y : a} -> (f : a -> N) -> x = y -> f x = f y
cong' f Refl = Refl
