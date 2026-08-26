%default total

data NatT = ZZ | SS NatT

-- `m` is declared ERASED (`{0 m}`): implicit AND quantity 0, the other quadrant
-- from relimpl01's relevant `{k}`.
data Vec : NatT -> Type where
  VNil  : Vec ZZ
  VCons : {0 m : NatT} -> NatT -> Vec m -> Vec (SS m)

-- The scrutinee type `Vec n` leaves `n` free, so matching `VCons` does not force
-- `m`; binding it by name and RETURNING it uses an erased value relevantly, which
-- the multiplicity checker rejects.
getm : (n : NatT) -> Vec n -> NatT
getm n VNil = ZZ
getm n (VCons {m = mm} x rest) = mm
