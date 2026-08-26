%default total

-- Uninitialised signals (paper §5). Continuous signals carry an initialisation
-- flag (`Init`); a `switch` forces every residual output to be INITIALISED
-- (`initc bv`), preventing an uninitialised signal from escaping the switch's
-- local time0. Here the outputs are honestly initialised via `initc`, so the
-- computed output index `initc bv` matches on both sides — accept/accept.
-- Faithful transliteration of frp11_initc_switch.cure.

data Init = IIni | IUni
data Sig = SigC Init | SigE
data Dec = DDec | DCau

djoin : Dec -> Dec -> Dec
djoin DDec DDec = DDec
djoin _ _ = DCau

data SList = SNil | SCons Sig SList

initcAux : Sig -> Sig
initcAux (SigC i) = SigC IIni
initcAux SigE = SigE

initc : SList -> SList
initc SNil = SNil
initc (SCons x r) = SCons (initcAux x) (initc r)

data SF : SList -> SList -> Dec -> Type where
  Prim   : SF av bv DCau
  Dpre   : SF av bv DDec
  Switch : SF av (SCons SigE bv) d1 -> SF av bv d2 -> SF av (initc bv) (djoin d1 d2)

switchInit : {av, bv : SList} ->
             SF av (SCons SigE bv) DDec ->
             SF av bv DDec ->
             SF av (initc bv) DDec
switchInit initial residual = Switch initial residual
