%default total

data N = Z | S N

g : N -> N
g Z = Z
g (S k) = S k

foo : N -> N
foo n with (g n)
  foo n | Z = Z
  foo n | (S k) = Z
