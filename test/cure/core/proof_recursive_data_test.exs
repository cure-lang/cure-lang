defmodule Cure.Core.ProofRecursiveDataTest do
  @moduledoc """
  Fixed signature-aware observations, not universal execution or checker refinement.
  Agda independently replays layout guards, recursive proofs and original-goal safety.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, ProofRecipe, Quote}
  alias Cure.Test.{ProofDataSpineFixture, ProofRecursiveDataFixture}

  @root Path.expand("../../..", __DIR__)

  test "recursive data observations and the checking request are reproducible" do
    assert {:ok, generated} = ProofRecursiveDataFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableRecursiveData.agda")

    assert {:ok, characters} =
             ProofRecipe.encode_checking(ProofRecursiveDataFixture.checking_request(), ProofDataSpineFixture.table())

    assert String.starts_with?(characters, "(" <> String.duplicate("1", 20))
  end

  test "one signature recovers data slots beneath closures and constructor fields" do
    grade = Grade.unrestricted()
    canonical = {:data, :"Spine#Indexed", [{:atom_type}], [{:atom_lit, :payload}]}
    assert observed(:canonical) == canonical
    assert observed(:application) == canonical
    assert observed(:case) == canonical
    assert {:lam, ^grade, ^canonical, {:var, 0}} = observed(:domain)
    assert {:lam, ^grade, {:atom_type}, ^canonical} = observed(:body)
    assert {:lam, ^grade, {:atom_type}, ^canonical} = observed(:capture)
    assert {:pi, ^grade, ^canonical, ^canonical} = observed(:pi)
    assert {:ctor, :"Spine#Box", [^canonical]} = observed(:field)
  end

  test "signature-free actual fallback is distinct from signature-aware recursive readback" do
    {:nested, program, [], 0} = Enum.find(ProofRecursiveDataFixture.cases(), &(elem(&1, 0) == :nested))
    value = Eval.eval(program, [])
    refute Quote.reify(value, 0) == Quote.reify(value, 0, ProofDataSpineFixture.environment())
    assert observed(:open) == {:data, :"Spine#Indexed", [{:atom_type}], [{:var, 0}]}
  end

  defp observed(key) do
    {^key, program, env, depth} = Enum.find(ProofRecursiveDataFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), depth, ProofDataSpineFixture.environment())
  end
end
