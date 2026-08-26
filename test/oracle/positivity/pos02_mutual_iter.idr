%default total

data Opt a = ONone | OSome a

data Tok = MkTok

mutual
  data Iter a = MkIter (Tok -> Opt (IterStep a))
  data IterStep a = Yield a (Iter a)
