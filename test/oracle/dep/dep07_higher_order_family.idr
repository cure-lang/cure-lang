%default total

data N = Z | S N

the2 : {F : N -> Type} -> ((n : N) -> F n) -> (m : N) -> F m
the2 g m = g m

test : (m : N) -> N
test m = the2 (\n => n) m
