%default total

data N = Z | S N

data SN : N -> Type where
  SZ : SN Z
  SS : {n : N} -> SN n -> SN (S n)

record DPair where
  constructor MkDPair
  fst : N
  snd : SN fst

mk : DPair
mk = MkDPair (S Z) (SS SZ)

getFst : DPair -> N
getFst p = p.fst
