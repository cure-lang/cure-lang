%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

record DPair where
  constructor MkDPair
  fst : N
  snd : SN fst

bad : DPair
bad = MkDPair (S Z) SZ
