defmodule Cure.Elab.LetInMatchBranchTest do
  @moduledoc """
  A BLOCK branch body (`let x = e in match x`) whose inner dependent match binds a
  proof whose index a later recursive call needs REDUCED.

  Before the fix, `elaborate_branch_body`'s catch-all elaborated a block body in
  INFERENCE mode, so the inner `match` on the let-bound variable never received the
  refined checking-mode goal. Its constructor-field index binders went unforced —
  the proof field kept its type over the OPAQUE erased index binders (`$erased_x`,
  `$erased_k`) instead of the scrutinee's concrete `x, k` — so a later
  reduction-requiring use (a recursive call's `boundLess(Only x, Only k)` domain,
  which ι-reduces to `strictLess(x, k)`) failed conversion at mismatched de Bruijn
  depths. The trigger needed THREE things at once: the `let`-bound scrutinee, a
  self-recursive call, and the reduction; remove any one and it already elaborated.

  The fix adds a `{:block}` branch-body clause that retries CHECKING mode against
  the branch goal, threading it through `elaborate_let_block` into the inner match
  so it reaches the index-forcing branch path — exactly as the direct form
  `Branch(k, match compareKeys(x, k), r)` (a ctor-call body) already did.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @bst """
    use Std.Equivalent
    type Key = Alpha | Beta | Gamma
    type Bit = No | Yes
    fn strictLess(x: Key, y: Key) -> Bit = match x
      Alpha() -> match y
        Alpha() -> No()
        Beta() -> Yes()
        Gamma() -> Yes()
      Beta() -> match y
        Alpha() -> No()
        Beta() -> No()
        Gamma() -> Yes()
      Gamma() -> match y
        Alpha() -> No()
        Beta() -> No()
        Gamma() -> No()
    type Bound = BelowAll | Only(Key) | AboveAll
    fn boundLess(lo: Bound, hi: Bound) -> Bit = match lo
      BelowAll() -> match hi
        BelowAll() -> No()
        Only(y) -> Yes()
        AboveAll() -> Yes()
      Only(x) -> match hi
        BelowAll() -> No()
        Only(y) -> strictLess(x, y)
        AboveAll() -> Yes()
      AboveAll() -> No()
    type Trichotomy indices (x: Key, k: Key)
      TriLess : Equivalent(Bit, strictLess(x, k), Yes()) -> Trichotomy(x, k)
      TriEqual : Equivalent(Key, x, k) -> Trichotomy(x, k)
      TriGreater : Equivalent(Bit, strictLess(k, x), Yes()) -> Trichotomy(x, k)
    fn compareKeys(x: Key, k: Key) -> Trichotomy(x, k) = match x
      Alpha() -> match k
        Alpha() -> TriEqual(reflexive(Alpha()))
        Beta() -> TriLess(reflexive(Yes()))
        Gamma() -> TriLess(reflexive(Yes()))
      Beta() -> match k
        Alpha() -> TriGreater(reflexive(Yes()))
        Beta() -> TriEqual(reflexive(Beta()))
        Gamma() -> TriLess(reflexive(Yes()))
      Gamma() -> match k
        Alpha() -> TriGreater(reflexive(Yes()))
        Beta() -> TriGreater(reflexive(Yes()))
        Gamma() -> TriEqual(reflexive(Gamma()))
    type SearchTree indices (lo: Bound, hi: Bound)
      Leaf : Equivalent(Bit, boundLess(lo, hi), Yes()) -> SearchTree(lo, hi)
      Branch : (k: Key) -> SearchTree(lo, Only(k)) -> SearchTree(Only(k), hi) -> SearchTree(lo, hi)
  """

  test "let-bound trichotomy scrutinee in a recursive insert branch elaborates" do
    src = """
    mod LetInMatchBst
    #{@bst}
      fn insert(lo: Bound, hi: Bound, x: Key, below: Equivalent(Bit, boundLess(lo, Only(x)), Yes()), above: Equivalent(Bit, boundLess(Only(x), hi), Yes()), t: SearchTree(lo, hi)) -> SearchTree(lo, hi) = match t
        Leaf(pf) -> Branch(x, Leaf(below), Leaf(above))
        Branch(k, l, r) -> let tri = compareKeys(x, k) in match tri
          TriLess(less) -> Branch(k, insert(lo, Only(k), x, below, less, l), r)
          TriEqual(eq) -> Branch(k, l, r)
          TriGreater(greater) -> Branch(k, l, insert(Only(k), hi, x, greater, above, r))
    end
    """

    assert {:ok, _} = Program.elaborate(src)
  end

  test "antibody: an ill-typed let-in-match recursive branch still rejects" do
    # In the TriLess branch, `less : strictLess(x,k)=Yes` is the only proof of the
    # left bound `boundLess(Only x, Only k)=Yes`. Passing `above` (a proof about the
    # OUTER hi bound) into the left subtree's slot is ill-typed and must not be
    # laundered into an accept by the checking-mode retry.
    src = """
    mod LetInMatchAntibody
    #{@bst}
      fn insert(lo: Bound, hi: Bound, x: Key, below: Equivalent(Bit, boundLess(lo, Only(x)), Yes()), above: Equivalent(Bit, boundLess(Only(x), hi), Yes()), t: SearchTree(lo, hi)) -> SearchTree(lo, hi) = match t
        Leaf(pf) -> Branch(x, Leaf(below), Leaf(above))
        Branch(k, l, r) -> let tri = compareKeys(x, k) in match tri
          TriLess(less) -> Branch(k, insert(lo, Only(k), x, below, above, l), r)
          TriEqual(eq) -> Branch(k, l, r)
          TriGreater(greater) -> Branch(k, l, insert(Only(k), hi, x, greater, above, r))
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
