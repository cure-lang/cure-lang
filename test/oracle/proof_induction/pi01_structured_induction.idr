%default total

data N = Z | S N

plus : N -> N -> N
plus Z right = right
plus (S previous) right = S (plus previous right)

plusZeroRight : (value : N) -> plus value Z = value
plusZeroRight Z = Refl
plusZeroRight (S previous) = rewrite plusZeroRight previous in Refl
