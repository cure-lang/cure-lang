%default total

-- Switch and the JOIN (`∨`) on decoupledness (paper §3.3.2 / §4). A `switch`
-- runs an initial signal function until its head event fires, then swaps in a
-- residual. Its decoupledness is `djoin d1 d2` (the paper's `∨`): decoupled only
-- if BOTH the initial and the residual are decoupled. `djoin DDec DDec = DDec`,
-- so switching two decoupled networks stays decoupled — accept/accept. The join
-- counterpart of frp02's meet. Faithful transliteration of frp09_switch_join.cure.

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

switchDec : {av, bv : SList} ->
            SF av (SCons SigE bv) DDec ->
            SF av bv DDec ->
            SF av bv DDec
switchDec initial residual = Switch initial residual
