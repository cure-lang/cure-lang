defmodule Cure.Core.TermLiteralsTest do
  @moduledoc """
  W3 audit red-green (pre-port banking spec §7 / gate 4, D4): the literal and
  type-constant Core forms — `{:int_type}`, `{:int_lit, _}`, `{:bool_type}`,
  `{:bool_lit, _}`, `{:float_type}`, `{:float_lit, _}` (the complete set; see
  `Eval.eval`, `Quote.reify`, `Kernel.rigid_index?`) — are first-class terms
  everywhere in the kernel EXCEPT `Cure.Core.Term`, whose `shift/3`, `subst/3`,
  and `term?/1` had no clauses for them. The first literal index to reach
  `unify_indices` (an `IxN`-style literal-indexed family) crashed the
  reify→shift preprocessing (`kernel.ex` `unify_indices`) with a
  FunctionClauseError BEFORE the deletion rule could see the equation `3 ~ 3`.

  Literals bind nothing and contain no de Bruijn variables, so `shift`/`subst`
  are identity on them and `term?` accepts them (with the payload type checked,
  matching the file's shape-check discipline).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Inductive, Kernel, Term}

  @dec {:data, :Dec, [], []}

  @literal_forms [
    {:int_type},
    {:int_lit, 3},
    {:int_lit, -7},
    {:float_type},
    {:float_lit, 1.5}
  ]

  test "shift/3 is identity on every literal/type-constant form" do
    for form <- @literal_forms do
      assert Term.shift(form, 1, 0) == form
      assert Term.shift(form, 5, 2) == form
    end
  end

  test "subst/3 is identity on every literal/type-constant form" do
    for form <- @literal_forms do
      assert Term.subst(form, 0, {:type, 0}) == form
    end
  end

  test "shift/3 and subst/3 traverse literals nested inside compound terms" do
    nested = {:ctor, :wrapn, [{:int_lit, 3}, {:var, 0}]}
    assert Term.shift(nested, 2, 0) == {:ctor, :wrapn, [{:int_lit, 3}, {:var, 2}]}

    assert Term.subst(nested, 0, {:int_lit, 5}) ==
             {:ctor, :wrapn, [{:int_lit, 3}, {:int_lit, 5}]}
  end

  test "term?/1 accepts every literal/type-constant form (well-typed payloads)" do
    for form <- @literal_forms do
      assert Term.term?(form), "term? rejected #{inspect(form)}"
    end

    # shape discipline: wrong payload types are still rejected
    refute Term.term?({:int_lit, :not_an_int})
    refute Term.term?({:float_lit, 2})
  end

  test "end-to-end: branch_unify over a literal-indexed family does not raise (W3 crash site)" do
    # IxN indexed by a raw integer; wrapn's ground result index is the literal 3.
    # A scrutinee index value {:vint, 3} produces the equation 3 ~ 3, which must
    # reach the deletion rule (r == s ⇒ consistent, no refinement ⇒ :trivial) —
    # pre-fix, reify→shift preprocessing crashed with FunctionClauseError first.
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [
        Inductive.ctor(:Dcoupled, [], []),
        Inductive.ctor(:Causal, [], [])
      ])
      |> Inductive.declare(Inductive.family(:IxN, [], [{:i, {:int_type}}], 0), [
        Inductive.ctor(:wrapn, [{:p, @dec}], [{:int_lit, 3}])
      ])

    ctx = Context.empty(env)
    assert :trivial = Kernel.branch_unify(ctx, :IxN, :wrapn, [{:vint, 3}])
  end
end
