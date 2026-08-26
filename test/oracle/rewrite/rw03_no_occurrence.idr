%default total

data N = Z | S N

noOccurrence : (p : the N Z = Z) -> (m : N) -> m = m
noOccurrence p m = rewrite p in Refl
