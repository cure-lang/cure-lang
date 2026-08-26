%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

-- syntactic multi-occurrence: `plus n Z` appears twice; one `rewrite` hits both
multiOcc : (n : N) -> plus (plus n Z) (plus n Z) = plus n n
multiOcc n = rewrite plusZeroRight n in Refl
