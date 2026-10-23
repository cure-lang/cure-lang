defmodule Cure.Core.ProofConstructorTest do
  @moduledoc """
  Fixed terminating observation regressions, not universal execution refinement.
  Formal model simulation and conditional safety are checked independently in Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.{ProofConstructorFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "the recursive constructor artifact is reproducible" do
    assert {:ok, generated} = ProofConstructorFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableConstructor.agda")
  end

  test "field redexes, nested constructors and closure captures reify structurally" do
    grade = Grade.unrestricted()
    assert observed(:redex) == observed(:packed)

    assert {:ctor, :"Boundary#Pack",
            [{:atom_type}, {:ctor, :"Boundary#Alternate", [{:atom_type}, {:atom_lit, :payload}]}]} = observed(:nested)

    assert {:ctor, :"Boundary#Pack", [{:lam, ^grade, {:atom_type}, {:var, 0}}]} = observed(:field_closure)
    assert {:lam, ^grade, {:atom_type}, {:ctor, :"Boundary#Pack", _fields}} = observed(:captured)
    assert {:lam, ^grade, {:atom_type}, {:ctor, :"Boundary#Pack", [{:atom_type}, {:var, 0}]}} = observed(:under_binder)
  end

  test "exact cases return constructor fields and constructor-valued bodies" do
    assert observed(:case_tree) == observed(:nested)
    assert {:ctor, :"Boundary#Alternate", [{:atom_type}, {:atom_lit, :payload}]} = observed(:case_field)
  end

  test "compact constructors and signature-free data splitting are separate contracts" do
    assert {:bounded_lit, 0} = Quote.reify(Eval.eval({:ctor, :First, [{:atom_type}]}, []), 0)
    program = {:data, :"Boundary#Packed", [], [{:atom_type}]}
    value = Eval.eval(program, [])
    assert {:data, :"Boundary#Packed", [{:atom_type}], []} = Quote.reify(value, 0)
    assert Quote.reify(value, 0, ProofSnapshotFixture.environment()) == program
  end

  defp observed(key) do
    {^key, program, env, depth} = Enum.find(ProofConstructorFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), depth)
  end
end
