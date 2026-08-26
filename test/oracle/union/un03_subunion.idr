%default total

-- Widening a narrower union into a wider one, and a sub-union match arm. In Idris2
-- both are explicit functions over named sums; in Cure the elaborator generates the
-- remap, but it is still a REAL function (a case), never a cast.
data Narrow = NInt Int | NBool Bool
data Wide = WInt Int | WBool Bool | WAtom String

narrow : Int -> Narrow
narrow n = NInt n

widen : Int -> Wide
widen n = case narrow n of
            NInt i  => WInt i
            NBool b => WBool b

split : Wide -> Int
split (WInt n)  = n
split (WBool _) = 0
split (WAtom _) = 0
