%default total

-- Packing an erased index `{d : Dec}` into the FIRST component of a dependent
-- pair `(x : Dec ** SF as bs x)`. The Sigma's fst is a runtime-relevant value,
-- so materialising the erased `d` there is a linearity/accessibility error in
-- Idris. Cure keeps both Sigma components at runtime (Erase.erase), so the same
-- pack drops `d`'s slot while `%[d, sf]` still references it — the {0,ω} check
-- rejects it. Expect reject/reject.

data Dec = Dcoupled | Causal
data Sig = CSig | ESig
data SVDesc = SVNil | SVCons Sig SVDesc

andd : Dec -> Dec -> Dec
andd x y = x

data SF : SVDesc -> SVDesc -> Dec -> Type where
  Prim : SF as bs Causal
  Seq  : SF as bs d1 -> SF bs cs d2 -> SF as cs (andd d1 d2)

forgetDec : {as : SVDesc} -> {bs : SVDesc} -> {d : Dec} -> SF as bs d -> (x : Dec ** SF as bs x)
forgetDec sf = (d ** sf)
