defmodule Cure.Core.ProofResidualNormalTest do
  @moduledoc """
  Fixed residual Quote observations, not a universal normalizer refinement.
  Signature-relative forms and administrative provenance are checked in Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.{ProofResidualNormalFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "the reviewed residual observations are reproducible" do
    assert {:ok, generated} = ProofResidualNormalFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableResidualNormal.agda")
  end

  test "branch and motive redexes normalize without eliminating an opaque scrutinee" do
    {program, opaque} = observed(:opaque)
    assert opaque == program
    assert {_, ^opaque} = observed(:branch)
    assert {_, ^opaque} = observed(:motive)
    assert {:case, {:global, :"Boundary#packed"}, _motive, [_first, _second]} = opaque
  end

  test "residual cases survive under binders, constructors and data" do
    grade = Grade.unrestricted()
    {_, opaque} = observed(:opaque)
    assert {_, {:lam, ^grade, {:atom_type}, ^opaque}} = observed(:lambda)
    assert {_, {:ctor, :"Boundary#Pack", [{:atom_type}, ^opaque]}} = observed(:ctor)
    assert {_, {:data, :"Boundary#Packed", [], [^opaque]}} = observed(:data)
    {nested_program, nested_quoted} = observed(:nested)
    assert nested_quoted == nested_program
  end

  test "Quote alone does not unfold a certified delta head" do
    assert {{:global, :"Boundary#answer"}, {:global, :"Boundary#answer"}} = observed(:delta)
    assert {_, {:atom_lit, :payload}} = observed(:beta)
  end

  defp observed(key) do
    {^key, program, env, depth} = Enum.find(ProofResidualNormalFixture.cases(), &(elem(&1, 0) == key))
    {program, Quote.reify(Eval.eval(program, env), depth, ProofSnapshotFixture.environment())}
  end
end
