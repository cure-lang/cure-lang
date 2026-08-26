%default total

-- E8 mirror: sequential-match / carried-index refinement. The `ENode` result
-- index is `Ev (Node a b) (add n1 n2)` — position 0 is a plain constructor spine
-- over the ctor's own variables, position 1 a computed measure. At the USE site
-- the scrutinee's index is `Node p (twist q)`: constructor-headed (`Node`) but
-- carrying a computed subterm `twist q`. Matching `ENode` unifies `Node p (twist q)`
-- against `Node a b` structurally (a := p, b := twist q) and refines the measure
-- `n := add n1 n2` into the goal, so `rewrite add_assoc (add n1 n2) k j` finds its
-- redex. Idris does this by ordinary dependent matching; Cure now does too — the
-- constructor-headed position is invertible by structural unification, so the
-- carried-eq detour that used to drop the measure refinement no longer misfires.
--
-- `n` is implicit here (determined by the `Ev` index); Cure spells it explicit.
-- Same program, each language's idiom.

data Sh = Leaf | Node Sh Sh

twist : Sh -> Sh
twist Leaf       = Leaf
twist (Node a b) = Node (twist b) (twist a)

public export
add : Nat -> Nat -> Nat
add Z     n = n
add (S k) n = S (add k n)

add_assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> add (add a b) c = add a (add b c)
add_assoc Z     b c = Refl
add_assoc (S k) b c = rewrite add_assoc k b c in Refl

data Ev : Sh -> Nat -> Type where
  ENode : (n1 : Nat) -> (n2 : Nat) -> Ev a n1 -> Ev b n2 -> Ev (Node a b) (add n1 n2)

ev_assoc : (p : Sh) -> (q : Sh) -> (k : Nat) -> (j : Nat) ->
           Ev (Node p (twist q)) n -> Ev (Node p (twist q)) n ->
           add (add n k) j = add n (add k j)
ev_assoc p q k j (ENode n1 n2 ea eb) sib = rewrite add_assoc (add n1 n2) k j in Refl
