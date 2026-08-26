%default total

data Nat' = Z | S Nat'
data Bool' = T | F

data Const : Type -> Type -> Type where
  MkConst : a -> Const a b

mk : {a : Type} -> {b : Type} -> a -> Const a b
mk x = MkConst x

use : Const Nat' Bool'
use = mk Z
