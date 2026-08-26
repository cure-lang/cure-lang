%default total

-- Multi-occurrence variant of frp01: unlike `parAssoc` (which rewrites the
-- input and output descriptors with two SEPARATE `appAssoc` rewrites over
-- distinct variables), here the SAME computed descriptor `(av ++ bv) ++ cv`
-- indexes BOTH the input and the output of one `SF`. Re-associating it is a
-- SINGLE `rewrite appAssoc av bv cv` that must abstract BOTH index occurrences
-- at once — the ∗∗-interchange "multiple occurrences, one rewrite" shape.

data Sig = SigC | SigE

data Dec = DDec | DCau

dmeet : Dec -> Dec -> Dec
dmeet DDec DDec = DDec
dmeet _ _ = DCau

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

-- one rewrite, two index occurrences (input AND output share the descriptor)
assocBoth : SF (app (app av bv) cv) (app (app av bv) cv) d
         -> SF (app av (app bv cv)) (app av (app bv cv)) d
assocBoth sf = rewrite appAssoc av bv cv in sf
