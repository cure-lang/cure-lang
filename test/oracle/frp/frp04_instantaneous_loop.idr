%default total

-- Capstone (ill-formed): an instantaneous feedback net. `loop` requires its body
-- to be DECOUPLED (`DDec`), but here the body is CAUSAL (`DCau`) — the fed-back
-- signal depends instantaneously on itself. `DCau /= DDec` at `Loop`'s argument
-- index, so this is a TYPE ERROR. The paper's safety property: instantaneous
-- cycles are statically rejected. Faithful transliteration of
-- frp04_instantaneous_loop.cure — reject/reject.

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

instantaneousCycle : {av, bv, cv : SList} ->
                     SF (app av cv) (app bv cv) DCau ->
                     SF av bv DCau
instantaneousCycle body = Loop body
