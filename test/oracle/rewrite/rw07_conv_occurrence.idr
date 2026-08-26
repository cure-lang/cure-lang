%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

convOccurrence : (n : N) -> plus (plus Z n) Z = n
convOccurrence n = rewrite plusZeroRight n in Refl
