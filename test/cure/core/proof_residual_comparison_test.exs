defmodule Cure.Core.ProofResidualComparisonTest do
  @moduledoc """
  Fixed terminating implementation observations. Agda independently checks
  positive residual conversion and native admission, not all actual Conv.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Conv, Eval, ProofRecipe, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofResidualComparisonFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "the residual comparison and checking artifact is reproducible" do
    assert {:ok, generated} = ProofResidualComparisonFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableResidualComparison.agda")
  end

  test "all four data-only requests need nonexact positive conversion" do
    assert [_, _, _, _] = requests = ProofResidualComparisonFixture.checking_cases()
    signature = ProofSnapshotFixture.environment()

    for {_key, {:checking, _subject, _recipe, _kind, goal, _goal_kind} = request, inferred} <- requests do
      refute inferred == goal
      assert {:ok, _characters} = ProofRecipe.encode_checking(request, ProofBundleFixture.table())
      assert Conv.conv?(inferred, goal, [], 0, signature)
      assert Quote.reify(Eval.eval(inferred, []), 0, signature) == Quote.reify(Eval.eval(goal, []), 0, signature)
    end
  end

  test "distinct eta and certified-delta readbacks are not conversion refutations" do
    signature = ProofSnapshotFixture.environment()
    comparisons = ProofResidualComparisonFixture.comparisons()

    for key <- [:eta_boundary, :delta_boundary] do
      {^key, left, right, env, depth} = Enum.find(comparisons, &(elem(&1, 0) == key))
      assert Conv.conv?(left, right, env, depth, signature)
      refute Quote.reify(Eval.eval(left, env), depth, signature) == Quote.reify(Eval.eval(right, env), depth, signature)
    end
  end
end
