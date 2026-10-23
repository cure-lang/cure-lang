defmodule Cure.Core.ProofNormalizingAdmissionTest do
  @moduledoc """
  Reviewed observation/producer regressions, not universal Conv soundness.
  Agda independently checks native positive comparison and expected-goal admission.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Conv, Eval, ProofRecipe, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofCheckingFixture, ProofComparisonFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "comparison and checking artifacts are reproducible" do
    assert {:ok, comparison} = ProofComparisonFixture.to_agda()
    assert comparison == File.read!(@root <> "/proof/Fixtures/ExecutableComparison.agda")
    assert {:ok, checking} = ProofCheckingFixture.to_agda()
    assert checking == File.read!(@root <> "/proof/Fixtures/ExecutableChecking.agda")
  end

  test "the checking producer uses tag 20 without a conversion recipe field" do
    assert {:ok, chars} = ProofRecipe.encode_checking(ProofCheckingFixture.request(), ProofBundleFixture.table())
    assert String.starts_with?(chars, "(" <> String.duplicate("1", 20) <> ";")
    assert {:checking, _subject, :r_leaf, :r_leaf, _goal, {:r_app, _, _}} = ProofCheckingFixture.request()
  end

  test "checking tuple, recipe and table errors propagate" do
    for request <- [
          {:checking},
          {:checking, {:atom_lit, :payload}, :r_leaf, :r_leaf, {:atom_type}},
          {:checking, {:atom_lit, :payload}, :c_refl, :r_leaf, {:atom_type}, :r_leaf}
        ] do
      assert {:error, {:malformed_recipe, _kind, _value}} =
               ProofRecipe.encode_checking(request, ProofBundleFixture.table())
    end

    assert {:error, {:malformed_table, _table}} =
             ProofRecipe.encode_checking(ProofCheckingFixture.request(), ["" | :improper])

    assert {:error, {:unknown_name, "payload"}} =
             ProofRecipe.encode_checking(ProofCheckingFixture.request(), [""])
  end

  test "eta, raw lambda domains and certified delta need not have identical quotes" do
    for key <- [:eta, :domain, :delta] do
      {^key, left, right, env, depth, with_signature} =
        Enum.find(ProofComparisonFixture.cases(), &(elem(&1, 0) == key))

      signature = if with_signature, do: ProofSnapshotFixture.environment()
      assert Conv.conv?(left, right, env, depth, signature)

      refute Quote.reify(Eval.eval(left, env), depth, signature) ==
               Quote.reify(Eval.eval(right, env), depth, signature)
    end
  end

  test "grades, universe levels and literal names remain distinct in actual comparison" do
    for key <- [:lambda_grade, :pi_grade, :universe, :name] do
      {^key, left, right, env, depth, with_signature} =
        Enum.find(ProofComparisonFixture.cases(), &(elem(&1, 0) == key))

      signature = if with_signature, do: ProofSnapshotFixture.environment()
      refute Conv.conv?(left, right, env, depth, signature)
    end
  end
end
