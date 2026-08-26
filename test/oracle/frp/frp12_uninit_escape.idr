%default total

-- The uninitialised-escape safety property (paper §5.2): a `switch` initialises
-- its residual outputs (`initc bv`), so an UNINITIALISED continuous signal
-- (`SigC IUni`) cannot escape. Claiming the switch outputs `SigC IUni` at the
-- head is a TYPE ERROR — `initc` forces the head to `SigC IIni`, and
-- `IIni /= IUni`. The paper's guarantee that uninitialised signals do not escape
-- a sub-network's local time0. Faithful transliteration of
-- frp12_uninit_escape.cure — reject/reject.

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

uninitEscape : {av, bv : SList} ->
               SF av (SCons SigE (SCons (SigC IUni) bv)) DDec ->
               SF av (SCons (SigC IUni) bv) DDec ->
               SF av (SCons (SigC IUni) bv) DDec
uninitEscape initial residual = Switch initial residual
