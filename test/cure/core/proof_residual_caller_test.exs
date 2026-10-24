defmodule Cure.Core.ProofResidualCallerTest do
  @moduledoc """
  Reviewed finite caller observations. Native context admission and coherent
  original-goal safety are checked independently in Agda, not by these data.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Conv, Eval, ProofRecipe, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofResidualCallerFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "paired caller packets and actual observations are reproducible" do
    assert {:ok, generated} = ProofResidualCallerFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableResidualCaller.agda")
  end

  test "the existing caller and ordinary-recipe encoders independently render every proposal" do
    for {_key, caller, kind, _inferred, _expected} <- ProofResidualCallerFixture.cases() do
      assert {:ok, _caller_chars} = ProofRecipe.encode_caller(caller, ProofBundleFixture.table())
      assert {:ok, _kind_chars} = ProofRecipe.encode_recipe(kind, ProofBundleFixture.table())
    end
  end

  test "open residual equality depends on fresh slots, not supplied closing arguments" do
    signature = ProofSnapshotFixture.environment()

    for {_key, {:caller, bindings, _, _arguments, _, _subject, goal, _, _}, _kind, inferred, expected} <-
          ProofResidualCallerFixture.cases() do
      size = length(bindings)
      env = if size == 0, do: [], else: Enum.map((size - 1)..0//-1, &{:vneutral, {:nvar, &1}})
      assert Conv.conv?(inferred, goal, env, size, signature) == expected

      quoted_equal? =
        Quote.reify(Eval.eval(inferred, env), size, signature) ==
          Quote.reify(Eval.eval(goal, env), size, signature)

      assert quoted_equal? == expected
    end
  end
end
