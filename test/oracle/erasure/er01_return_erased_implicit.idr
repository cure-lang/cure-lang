%default total

-- An erased implicit `{k : N}` returned as a runtime `N` result. Idris binds
-- implicits at multiplicity 0 (erased), so returning `k` in a runtime-relevant
-- position is a linearity/accessibility error. Cure marks `{k: Nat}` :erased and
-- the {0,ω} relevance check (M8.3) rejects the same use — expect reject/reject.

data N = Z | S N

data SNat : N -> Type where
  SZ : SNat Z
  SS : {n : N} -> SNat n -> SNat (S n)

rel : {k : N} -> SNat k -> N
rel x = k
