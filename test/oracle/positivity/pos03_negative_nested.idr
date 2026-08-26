%default total

data Void : Type where

data Neg t = MkNeg (t -> Void)

data Bad = MkBad (Neg Bad)
