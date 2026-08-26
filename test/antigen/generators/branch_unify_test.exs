defmodule Antigen.Generators.BranchUnifyTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.BranchUnify
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays}

  @sample 300

  test "every sampled branch-unify probe's verdict agrees with the live kernel" do
    for %Challenge{} = c <- B.interp(BranchUnify.gen()) |> Enum.take(@sample) do
      assert c.kind == :branch_unify
      assert c.label in [:trivial, :solved, :impossible, :bad_motive]

      assert Assays.BranchUnify.run(c) == :ok,
             "verdict oracle disagreed on #{c.note} (#{c.label})"
    end
  end

  test "the case menu spans all three verdicts and the key unifier arms" do
    labels = BranchUnify.cases() |> Enum.map(fn {_n, _d, _c, _i, v, _note} -> v end) |> MapSet.new()
    assert MapSet.equal?(labels, MapSet.new([:trivial, :solved, :impossible]))

    notes = BranchUnify.cases() |> Enum.map(fn t -> elem(t, 5) end)

    for frag <- ["merge conflict", "forced equation", "rigid data/Type", "outer index var", "multi-key cycle"] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing arm: #{frag}"
    end
  end

  # Finding S9: a family PARAMETER buried in a result-index spine (`MkFoo : Foo a
  # (S a)`) must not be mistaken for a cyclic self-occurrence. The pre-fix unifier
  # verdicted `:impossible` on the solvable branch; the assay drives `branch_unify/5`
  # with the scrutinee's actual param values to reach the fixed path.
  test "the parameterised-GADT (S9) menu carries scrutinee params and both verdicts" do
    labels = BranchUnify.param_cases() |> Enum.map(fn t -> elem(t, 5) end) |> MapSet.new()
    assert MapSet.equal?(labels, MapSet.new([:solved, :impossible]))

    # every param case carries a non-empty scrutinee-param vector (drives /5)
    assert Enum.all?(BranchUnify.param_cases(), fn t -> elem(t, 4) != [] end)
  end

  test "the S9 solvable branch is :solved, not :impossible (spurious-cycle regression)" do
    {n, d, c, idx, params, :solved, _note} =
      Enum.find(BranchUnify.param_cases(), fn t -> elem(t, 5) == :solved end)

    ch =
      Challenge.new(
        kind: :branch_unify,
        assay: "branchunify/verdict",
        label: :solved,
        payload: %{ctx_vars: n, dname: d, cname: c, indices: idx, params: params}
      )

    assert Assays.BranchUnify.run(ch) == :ok
  end
end
