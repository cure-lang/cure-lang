%default total

-- Capstone (well-formed): a feedback loop whose body is DECOUPLED (`DDec`) over
-- the fed-back signal `cv`. `Loop` requires exactly that, so the cycle is broken
-- and it accepts. Faithful transliteration of frp03_wellformed_loop.cure —
-- accept/accept.

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
  Par  : SF av bv d1 -> SF cv dv d2 -> SF (app av cv) (app bv dv) (dmeet d1 d2)
  Loop : SF (app av cv) (app bv cv) DDec -> SF av bv DCau

wellFormedLoop : {av, bv, cv : SList} ->
                 SF (app av cv) (app bv cv) DDec ->
                 SF av bv DCau
wellFormedLoop body = Loop body
