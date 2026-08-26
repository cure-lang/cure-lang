%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRightSym : (n : N) -> n = plus n Z
plusZeroRightSym Z = Refl
plusZeroRightSym (S k) = rewrite plusZeroRightSym k in Refl
