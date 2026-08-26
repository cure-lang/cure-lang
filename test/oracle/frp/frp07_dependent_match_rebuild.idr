%default total

-- A dependent match that RECONSTRUCTS the scrutinee constructor at the branch-
-- refined index. Idris types each branch body against that branch's refined
-- `SF as bs d`, pinning the (nullary) constructors' indices from the goal.
-- Faithful transliteration of frp07_dependent_match_rebuild.cure — accept/accept.

data Sig = SigC | SigE
data Dec = DDec | DCau

dmeet : Dec -> Dec -> Dec
dmeet DDec DDec = DDec
dmeet _ _ = DCau

data SList = SNil | SCons Sig SList

app : SList -> SList -> SList
app SNil ys = ys
app (SCons x xs) ys = SCons x (app xs ys)

data SF : SList -> SList -> Dec -> Type where
  Prim : SF av bv DCau
  Dpre : SF av bv DDec
  Seq  : SF av bv d1 -> SF bv cv d2 -> SF av cv (dmeet d1 d2)

ident : {as, bs : SList} -> {d : Dec} -> SF as bs d -> SF as bs d
ident s = case s of
  Prim => Prim
  Dpre => Dpre
  Seq l r => Seq l r
