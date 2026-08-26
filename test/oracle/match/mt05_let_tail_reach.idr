%default total

data N = Z | S N

pred : N -> N
pred n = let r = case n of
                   Z => Z
                   S k => k
         in r
