%default total

data N = Z | S N

mk : N -> N
mk = \y => S y
