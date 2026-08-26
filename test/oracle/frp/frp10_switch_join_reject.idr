%default total

-- The switch safety property (join). A `switch` whose INITIAL network is causal
-- (`DCau`) cannot be decoupled: `djoin DCau DDec = DCau /= DDec` at `Switch`'s
-- result index, so claiming the switch is `DDec` is a TYPE ERROR. The join
-- counterpart of frp04's instantaneous loop — the switch is decoupled only if
-- the initial network is too. Faithful transliteration of
-- frp10_switch_join_reject.cure — reject/reject.

data Sig = SigC | SigE
data Dec = DDec | DCau

djoin : Dec -> Dec -> Dec
djoin DDec DDec = DDec
djoin _ _ = DCau

data SList = SNil | SCons Sig SList

data SF : SList -> SList -> Dec -> Type where
  Prim   : SF av bv DCau
  Dpre   : SF av bv DDec
  Switch : SF av (SCons SigE bv) d1 -> SF av bv d2 -> SF av bv (djoin d1 d2)

switchCausal : {av, bv : SList} ->
               SF av (SCons SigE bv) DCau ->
               SF av bv DDec ->
               SF av bv DDec
switchCausal initial residual = Switch initial residual
