%default total

data N = Z | S N

plus : N -> N -> N
plus Z n = n
plus (S k) n = S (plus k n)

plusZeroRight : (n : N) -> plus n Z = n
plusZeroRight Z = Refl
plusZeroRight (S k) = rewrite plusZeroRight k in Refl

plusSuccRight : (m : N) -> (n : N) -> plus m (S n) = S (plus m n)
plusSuccRight Z n = Refl
plusSuccRight (S k) n = rewrite plusSuccRight k n in Refl

plusComm : (m : N) -> (n : N) -> plus m n = plus n m
plusComm Z n = rewrite plusZeroRight n in Refl
plusComm (S k) n = rewrite plusSuccRight n k in rewrite plusComm k n in Refl
