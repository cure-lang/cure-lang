%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRightBad : (n : N) -> plus n Z = n
plusZeroRightBad n = Refl
