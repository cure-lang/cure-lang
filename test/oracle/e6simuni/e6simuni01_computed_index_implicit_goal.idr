%default total

-- SIMULTANEOUS-UNIFICATION / computed-index constructor at an IMPLICIT goal.
--
-- `ATimes`'s result index is `Acc (PTimes l r) (add m1 m2)` — position 0 a plain
-- constructor spine over the ctor's own index variables, position 1 a COMPUTED
-- measure. At the use site the goal is `Acc (PTimes (PA a) (PStar (PA a))) (S Z)`
-- where `a` is an implicit the caller must solve. Position 0 determines `a`
-- structurally from the present arguments; position 1 (`add m1 m2`) stays stuck
-- until `m1`, `m2` are pinned by `AAtomA`/`AStar`. Idris solves this by ordinary
-- dependent unification (it unifies the index vector component-wise, tolerating a
-- stuck component); Cure now does too via component-wise `unify_data_components`.
-- `a` is implicit in both — same program, each language's idiom.

data Tag = TA | TB

data Pat = PA Tag | PStar Pat | PTimes Pat Pat

add : Nat -> Nat -> Nat
add Z     n = n
add (S k) n = S (add k n)

data Acc : Pat -> Nat -> Type where
  AAtomA : Acc (PA TA) (S Z)
  AStar  : Acc (PStar q) Z
  ATimes : Acc l m1 -> Acc r m2 -> Acc (PTimes l r) (add m1 m2)

star_fold : {a : Tag} -> Acc (PTimes (PA a) (PStar (PA a))) (S Z) -> Unit
star_fold _ = ()

use : Unit
use = star_fold (ATimes AAtomA AStar)
