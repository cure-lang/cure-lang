%default total

-- SOUNDNESS BOUNDARY for the sim-unification fix. Identical to probe 01 except the
-- goal measure is `S (S Z)` while the present arguments force measure
-- `add (S Z) Z = S Z`. Idris solves the implicit `a` from position 0 (the `PTimes`
-- spine) but the measure equation `S Z = S (S Z)` fails, so it rejects — exactly as
-- Cure does: the tolerated stuck component is still genuinely checked once pinned.

data Tag = TA | TB

data Pat = PA Tag | PStar Pat | PTimes Pat Pat

add : Nat -> Nat -> Nat
add Z     n = n
add (S k) n = S (add k n)

data Acc : Pat -> Nat -> Type where
  AAtomA : Acc (PA TA) (S Z)
  AStar  : Acc (PStar q) Z
  ATimes : Acc l m1 -> Acc r m2 -> Acc (PTimes l r) (add m1 m2)

star_fold : {a : Tag} -> Acc (PTimes (PA a) (PStar (PA a))) (S (S Z)) -> Unit
star_fold _ = ()

use : Unit
use = star_fold (ATimes AAtomA AStar)
