%default total

-- A COMPOSED feedback loop: the body is `Seq` of two decoupled stages, so its
-- decoupledness is the computed `dmeet DDec DDec`. `Loop` requires `DDec`, so
-- feeding `Seq a b` to it needs `dmeet DDec DDec` reduced where the argument is
-- checked. Idris reduces it and accepts. Faithful transliteration of
-- frp06_composed_loop.cure — accept/accept.

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
  Loop : SF (app av cv) (app bv cv) DDec -> SF av bv DCau

composedLoop : {av, bv, cv, mv : SList} ->
               SF (app av cv) mv DDec ->
               SF mv (app bv cv) DDec ->
               SF av bv DCau
composedLoop a b = Loop (Seq a b)
