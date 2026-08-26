%default total

data NatT = ZZ | SS NatT

data Vec : NatT -> Type where
  VNil  : Vec ZZ
  VCons : NatT -> Vec m -> Vec (SS m)

-- A RELEVANT implicit constructor index: `{k : NatT}` is implicit (solved, not
-- passed positionally) yet unrestricted (retained, usable). Box carries no index
-- mentioning k, so k is redundant to pass yet still needed as a value.
data Box : Type where
  MkBox : {k : NatT} -> Vec k -> Box

-- Construct with k OMITTED — solved from the Vec k argument's index.
ex : Box
ex = MkBox (VCons ZZ VNil)

-- Pattern-bind k by name and RETURN it: accepted iff k is relevant (unrestricted).
getk : Box -> NatT
getk (MkBox {k = kk} v) = kk
