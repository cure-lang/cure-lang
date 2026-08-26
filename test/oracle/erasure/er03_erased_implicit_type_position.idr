%default total

-- Control: the erased implicit `{k : N}` appears ONLY in type positions (the
-- parameter type `SNat k` and the result type `SNat k`); the body returns the
-- runtime-relevant `a`. This is the normal, sound use of erasure and must be
-- accepted by both languages — expect accept/accept.

data N = Z | S N

data SNat : N -> Type where
  SZ : SNat Z
  SS : {n : N} -> SNat n -> SNat (S n)

idx : {k : N} -> SNat k -> SNat k
idx x = x
