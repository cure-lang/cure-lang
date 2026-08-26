%default total

data N = Z | S N

g : N -> N
g Z = Z
g (S k) = S k

lemma : (a : N) -> (b : N) -> a = b -> N
lemma a b eq = b

foo : (n : N) -> N
foo n with (g n) proof prf
  foo n | Z = lemma (g n) Z prf
  foo n | (S k) = lemma (g n) (S k) prf
