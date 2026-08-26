%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

-- conversion multi-occurrence: `plus Z n` reduces to `n`, so `plus n Z` is
-- present only up-to-conversion, twice; one `rewrite` must handle both
multiConv : (n : N)
         -> plus (plus (plus Z n) Z) (plus (plus Z n) Z) = plus n n
multiConv n = rewrite plusZeroRight n in Refl
