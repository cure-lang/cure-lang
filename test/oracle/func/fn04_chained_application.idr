%default total

data N = Z | S N

mk : N -> N
mk = \y => S y

g : N -> N
g z = mk z
