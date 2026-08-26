%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroLeft : (n : N) -> plus Z n = n
plusZeroLeft n = Refl
