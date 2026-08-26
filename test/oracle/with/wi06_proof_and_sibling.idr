%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

g : N -> N
g Z = Z
g (S k) = S k

consume : (m : N) -> SN m -> N
consume m s = m

lemma : (a : N) -> (b : N) -> a = b -> N
lemma a b e = b

foo : (n : N) -> SN (g n) -> N
foo n pf with (g n) proof eqp
  foo n pf | Z = consume (lemma (g n) Z eqp) pf
  foo n pf | (S k) = consume (lemma (g n) (S k) eqp) pf
