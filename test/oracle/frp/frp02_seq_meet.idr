%default total

-- Companion to frp01 that isolates the `Dec`-index (decoupledness) path from
-- the list-index (`++`) path: sequential composition `_≫_` (`Seq`) refines its
-- result index by `dmeet` (the paper's `∧` on decoupledness), with NO `++`
-- obligation. `seqDec` type-checks purely by computing `dmeet DDec DDec = DDec`
-- — no `rewrite`, no stuck index — so it should be accept/accept in both
-- languages, pinning the Dec path as the non-blocking baseline.

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
  Seq  : SF av bv d1 -> SF bv cv d2 -> SF av cv (dmeet d1 d2)
  Par  : SF av bv d1 -> SF cv dv d2 -> SF (app av cv) (app bv dv) (dmeet d1 d2)

-- Dec-index refinement only: `Seq` of two decoupled stages is decoupled,
-- witnessed by `dmeet DDec DDec` computing to `DDec`.
seqDec : SF av bv DDec -> SF bv cv DDec -> SF av cv DDec
seqDec x y = Seq x y
