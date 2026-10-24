defmodule Cure.Core.ProofResidualQuotationTest do
  @moduledoc """
  Fixed actual residual observations. Native refinement is independently
  checked in Agda; raw operational success is not a typing certificate.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Quote}
  alias Cure.Test.{ProofResidualQuotationFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "the actual recursive residual artifact is reproducible" do
    assert {:ok, generated} = ProofResidualQuotationFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableResidualQuotation.agda")
  end

  test "nested heads, branches and motives remain residual" do
    assert {:case, {:case, _, _, _}, _, _} = observed(:nested_scrutinee)
    assert {:case, _, _, [{:"Boundary#Pack", 2, {:case, _, _, _}}]} = observed(:nested_branch)
    assert {:case, _, {:case, _, _, _}, _} = observed(:nested_motive)
  end

  test "residual values survive eager evaluation, exact cases and captured binders" do
    opaque = observed(:opaque)
    assert observed(:beta_argument) == opaque
    assert observed(:exact_case) == opaque
    assert {:lam, _, {:atom_type}, ^opaque} = observed(:let_capture)
    assert {:lam, _, {:atom_type}, ^opaque} = observed(:environment)
    assert {:ctor, :"Boundary#Pack", [{:atom_type}, ^opaque]} = observed(:ctor_field)
    assert {:data, :"Boundary#Packed", [], [^opaque]} = observed(:data_index)
    assert {:app, ^opaque, {:atom_lit, :payload}} = observed(:neutral_function)
  end

  defp observed(key) do
    {^key, program, env, depth} = Enum.find(ProofResidualQuotationFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), depth, ProofSnapshotFixture.environment())
  end
end
