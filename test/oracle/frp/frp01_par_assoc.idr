%default total

-- Minimal faithful core of Sculthorpe & Nilsson's Safe-FRP `SF` family
-- (ICFP'09). The family is indexed by two type-level signal-vector
-- descriptors (here a self-contained `SList` of `Sig`) and a decoupledness
-- flag `Dec`; `_∗∗_` (parallel composition, `Par`) carries the *computed*
-- indices `av ++ cv` / `bv ++ dv`. Re-associating parallel composition is
-- exactly the `++`-associativity obligation §8 records the authors switching
-- from Haskell to Agda to discharge. `parAssoc` is the acceptance driver: its
-- well-typedness *requires* `++` associativity, discharged by `rewrite`.

data Sig = SigC | SigE

data Dec = DDec | DCau

dmeet : Dec -> Dec -> Dec
dmeet DDec DDec = DDec
dmeet _ _ = DCau

-- self-contained type-level list of signal descriptors (the paper's SVDesc)
data SList = SNil | SCons Sig SList

app : SList -> SList -> SList
app SNil ys = ys
app (SCons x xs) ys = SCons x (app xs ys)

appAssoc : (xs : SList) -> (ys : SList) -> (zs : SList)
        -> app xs (app ys zs) = app (app xs ys) zs
appAssoc SNil ys zs = Refl
appAssoc (SCons x xs) ys zs = rewrite appAssoc xs ys zs in Refl

data SF : SList -> SList -> Dec -> Type where
  Prim : SF av bv DCau
  Seq  : SF av bv d1 -> SF bv cv d2 -> SF av cv (dmeet d1 d2)
  Par  : SF av bv d1 -> SF cv dv d2 -> SF (app av cv) (app bv dv) (dmeet d1 d2)

-- acceptance driver: re-associating a parallel-composition witness needs
-- (av ++ bv) ++ cv = av ++ (bv ++ cv) on BOTH the input and output descriptors.
parAssoc : SF (app (app av bv) cv) (app (app xv yv) zv) d
        -> SF (app av (app bv cv)) (app xv (app yv zv)) d
parAssoc sf = rewrite appAssoc av bv cv in rewrite appAssoc xv yv zv in sf
