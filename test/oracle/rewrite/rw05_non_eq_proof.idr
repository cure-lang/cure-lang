%default total

data N = Z | S N

nonEqProof : (n : N) -> (m : N) -> m = m
nonEqProof n m = rewrite n in Refl
