defmodule Cure.Elab.CarriedIndexSiblingTest do
  @moduledoc """
  Phase 2 Step 3b — sibling refinement (the genuine carried equation).

  Step 3a refines each branch's GOAL to the constructor's computed result index
  via the motive (`match v` on `v : F(app(p,q))` gives goal `F(SNil())` in the
  `leaf` branch, `F(app(as,bs))` in `mk`). That is sound and needs no equation.

  But a SIBLING in the context — a second variable `w : F(app(p,q))` that is not
  the scrutinee — is NOT abstracted by the scrutinee's motive, so it keeps its
  original index. In the `leaf` branch the goal is refined to `F(SNil())` while
  `w` still has type `F(app(p,q))`; returning `w` there requires transporting it
  along the branch's stuck equation `app(p,q) = SNil()`. This is exactly Lean's
  opt-in `match h :` equation (`Match.lean:132-143`, gated on `hName?`): the
  equation reconciles the SCRUTINEE index against the branch index at the use
  site, a mechanism distinct from the motive goal refinement of 3a.

  RED until Step 3b carries `Eq(SList, app(p,q), <branch index>)` into the branch
  and transports index-mentioning siblings (capability-B Eq-arrow + `rewrite`,
  generalized value → index). The soundness control returns a sibling of the
  WRONG family index and must stay rejected.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  @preamble """
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type F indices (xs: SList)
      leaf : F(SNil())
      mk : F(as) -> F(bs) -> F(app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
    type ParameterizedF(tag: SList) indices (xs: SList)
      parameterized_leaf : ParameterizedF(tag, SNil())
      parameterized_mk : ParameterizedF(tag, as) -> ParameterizedF(tag, bs) -> ParameterizedF(tag, app(as, bs))
    type Depends(a: Type) indices (value: a)
      depends : (value: a) -> Depends(a, value)
    fn consume_dep({a: Type}, value: a, proof: Depends(a, value)) -> Nat = Z()
    @reducible
    fn nplus(left: Nat, right: Nat) -> Nat = match left
      Z() -> right
      S(prior) -> S(nplus(prior, right))
    type NestedOuter indices (head: Nat, total: Nat)
      nested_outer : (suffix: Nat) -> NestedOuter(head, nplus(head, suffix))
    type ZeroView indices (value: Nat)
      zero_exact : ZeroView(Z())
    type NatHold indices (value: Nat)
      nat_hold : NatHold(value)
    fn consume_hold(value: Nat, proof: NatHold(value)) -> Nat = value
  """

  defp mod(body), do: "mod P\n  type Nat = Z | S(Nat)\n" <> @preamble <> body <> "end\n"

  test "returning a sibling in a refined branch needs the carried index eq (3b)" do
    # `w : F(app(p,q))` is a sibling, not the scrutinee. In the `leaf` branch the
    # 3a-refined goal is `F(SNil())`; `w : F(app(p,q))` type-checks there only if
    # `app(p,q) = SNil()` is carried and `w` transported. Same for the `mk` arm
    # (`app(p,q) = app(as,bs)`). RED until 3b.
    src =
      mod("""
        fn keep({p: SList}, {q: SList}, v: F(app(p, q)), w: F(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> w
            mk(l, r) -> w
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "multiple carried siblings retain the outer de Bruijn frame" do
    # Each transported domain is authored in the same branch_ctx1 frame. After
    # `first` is rebound, the domain for `second` must be shifted past that new
    # binder before evaluation; otherwise its outer references resolve to the
    # value of `first` (the failure exposed by the dependent regex proof).
    src =
      mod("""
        fn keep_second({p: SList}, {q: SList}, v: F(app(p, q)), first: F(app(p, q)), second: F(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> second
            mk(l, r) -> second
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "three carried siblings survive dependent telescope discharge" do
    src =
      mod("""
        fn keep_third({p: SList}, {q: SList}, v: F(app(p, q)), first: F(app(p, q)), second: F(app(p, q)), third: F(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> third
            mk(l, r) -> third
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "carried-index motive preserves parameter binders in canonical order" do
    # The carried Eq wrapper peels and rebuilds all index/scrutinee motive
    # lambdas. Rebuilding an outermost-first list with a left fold reverses those
    # binders, placing the scrutinee domain outside the index binders it was
    # shifted beneath. A family parameter that names an outer function binder
    # then becomes a free de Bruijn variable in Final Core.
    src =
      mod("""
        fn keep_parameter({tag: SList}, {p: SList}, {q: SList}, v: ParameterizedF(tag, app(p, q)), sibling: ParameterizedF(tag, app(p, q))) -> ParameterizedF(tag, app(p, q)) =
          match v
            parameterized_leaf() -> sibling
            parameterized_mk(l, r) -> sibling
      """)

    assert {:ok, env} = Program.elaborate(src)
    assert Cure.Core.Term.closed?(Cure.Core.Env.get_def(env, :"P#keep_parameter").body)
  end

  test "a later carried sibling is reindexed by the transported earlier sibling" do
    # `second` depends on both the refined family index and the VALUE of `first`.
    # Rebinding only its de Bruijn frame leaves it indexed by the original
    # `first`; it must instead refer to the transported `first` introduced in
    # the branch context.
    src =
      mod("""
        fn keep_dependent({p: SList}, {q: SList}, v: F(app(p, q)), first: F(app(p, q)), second: Depends(F(app(p, q)), first)) -> Nat =
          match v
            leaf() -> consume_dep(first, second)
            mk(l, r) -> consume_dep(first, second)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a carried branch goal is reindexed by the transported sibling values" do
    # The branch goal itself mentions both transported siblings: its family
    # index contains the carried index, and its value index is `first`. Rebinding
    # only the branch context leaves the goal pointing at the original outer
    # `first`, so returning the transported `second` is rejected even though it
    # is definitionally the requested proof.
    src =
      mod("""
        fn keep_dependent_proof({p: SList}, {q: SList}, v: F(app(p, q)), first: F(app(p, q)), second: Depends(F(app(p, q)), first)) -> Depends(F(app(p, q)), first) =
          match v
            leaf() -> second
            mk(l, r) -> second
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "nested carried matches do not re-transport synthetic proof binders" do
    # The outer match introduces `$carried_idx_prf`. It is compiler evidence, not
    # an addressable source sibling; collecting it again in the inner match used
    # to recursively inflate the transported telescope and leave family bounds
    # as unsolved metavariables.
    src =
      mod("""
        fn nested({p: SList}, {q: SList}, v: F(app(p, q)), first: F(app(p, q)), second: Depends(F(app(p, q)), first)) -> Nat =
          match v
            leaf() -> match first
              leaf() -> consume_dep(first, second)
              mk(fl, fr) -> consume_dep(first, second)
            mk(l, r) -> match first
              leaf() -> consume_dep(first, second)
              mk(fl, fr) -> consume_dep(first, second)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "nested branch refinement composes through contextual values" do
    # The outer branch records `total = nplus(head, suffix)` in the context
    # environment. The inner branch then records `head = Z`. Specializing only
    # direct environment variables leaves the stored value for `total` stuck at
    # the old `head`, even though context TYPES are correctly rewritten. The
    # nested substitution must enter that prior value, reducing `total` to
    # `suffix`, so the explicit `total` argument agrees with `proof`'s index.
    src =
      mod("""
        fn nested_context_value(head: Nat, total: Nat, outer: NestedOuter(head, total), view: ZeroView(head), proof: NatHold(total)) -> Nat =
          match outer
            nested_outer(suffix) -> match view
              zero_exact() -> consume_hold(total, proof)
      """)

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "carried sibling eq does not admit a wrong-family sibling (soundness control)" do
    # `u : G(app(p,q))` DOES mention the carried index, so 3b transports it — in
    # the `leaf` branch to `G(SNil())`. But the goal there is `F(SNil())`, and
    # `G(SNil()) ≢ F(SNil())`: the transport fires yet the kernel still rejects on
    # the family mismatch. This exercises the transport path (not the 3a fallback)
    # and proves it does not launder an ill-typed result.
    src =
      mod("""
        fn bad({p: SList}, {q: SList}, v: F(app(p, q)), u: G(app(p, q))) -> F(app(p, q)) =
          match v
            leaf() -> u
            mk(l, r) -> u
      """)

    assert {:error, _} = Program.elaborate(src)
  end

  test "an unrelated-index sibling is not transported and stays rejected" do
    # `u : F(q)` does not mention `app(p,q)`, so 3b does not fire for it; the plain
    # 3a-refined goal (`F(SNil())` in `leaf`) rejects `u : F(q)`. Guards the
    # detection: a sibling on a different index must not be spuriously refined.
    src =
      mod("""
        fn bad({p: SList}, {q: SList}, v: F(app(p, q)), u: F(q)) -> F(app(p, q)) =
          match v
            leaf() -> u
            mk(l, r) -> u
      """)

    assert {:error, _} = Program.elaborate(src)
  end
end
