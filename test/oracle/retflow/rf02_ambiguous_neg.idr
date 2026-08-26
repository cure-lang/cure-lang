%default total

data Nat' = Z | S Nat'
data Bool' = T | F

mk : {a : Type} -> {b : Type} -> a -> a
mk x = x

use : Nat'
use = mk Z
