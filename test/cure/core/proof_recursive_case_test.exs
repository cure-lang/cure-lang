defmodule Cure.Core.ProofRecursiveCaseTest do
  @moduledoc """
  Fixed terminating observations, not universal execution refinement.
  General recursive simulation and original-goal safety are checked in Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.ProofRecursiveCaseFixture

  @root Path.expand("../../..", __DIR__)

  test "the recursive-case artifact is reproducible" do
    assert {:ok, generated} = ProofRecursiveCaseFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableRecursiveCase.agda")
  end

  test "nested case scrutinees and selected bodies share evaluation" do
    for key <- [:unpack, :scrutinee, :body, :application] do
      assert observed(key) == {:atom_lit, :payload}
    end

    assert {:ctor, :"Boundary#Pack", [{:atom_type}, {:atom_lit, :payload}]} = observed(:field)
    assert observed(:outer) == {:atom_lit, :hidden}
  end

  test "readback evaluates cases inside closure bodies and domains" do
    grade = Grade.unrestricted()
    assert {:lam, ^grade, {:atom_type}, {:var, 0}} = observed(:lambda)
    assert {:lam, ^grade, {:atom_type}, {:atom_lit, :payload}} = observed(:capture)
    assert {:pi, ^grade, {:atom_type}, {:atom_type}} = observed(:pi)
    assert observed(:type) == {:atom_type}
    assert Quote.reify(Eval.eval(ProofRecursiveCaseFixture.type_case(), []), 0) == {:atom_type}
  end

  test "actual neutral-case readback stays outside the positive exact-case model" do
    program =
      {:lam, Grade.unrestricted(), {:atom_type}, {:case, {:var, 0}, {:atom_type}, [{:"Boundary#Pack", 2, {:var, 0}}]}}

    assert Quote.reify(Eval.eval(program, []), 0) == program
  end

  defp observed(key) do
    {^key, program, env} = Enum.find(ProofRecursiveCaseFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), 0)
  end
end
