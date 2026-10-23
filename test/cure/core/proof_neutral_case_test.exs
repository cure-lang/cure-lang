defmodule Cure.Core.ProofNeutralCaseTest do
  @moduledoc """
  Fixed actual capture/readback regressions, not full shared neutral-case refinement.
  Scoped native simulation and original-goal safety are independently checked in Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Quote}
  alias Cure.Test.{ProofNeutralCaseFixture, ProofSnapshotFixture}

  @root Path.expand("../../..", __DIR__)

  test "the actual neutral capture/readback artifact is reproducible" do
    assert {:ok, generated} = ProofNeutralCaseFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableNeutralCase.agda")
  end

  test "motive and branch closures retain the case caller, not a scrutinee let frame" do
    {:capture, {:case, _scrutinee, motive, branches} = program, env, _depth} =
      Enum.find(ProofNeutralCaseFixture.cases(), &(elem(&1, 0) == :capture))

    assert [{:vatom, :payload}] = env

    assert {:vneutral, {:ncase, {:nglobal, :"Boundary#packed"}, {:closure, ^env, ^motive}, captured}} =
             Eval.eval(program, env)

    assert Enum.map(captured, fn {name, ar, {:closure, ^env, body}} -> {name, ar, body} end) == branches
  end

  test "branch, motive and computed-scrutinee readback recover the reviewed residual" do
    opaque = observed(:opaque)
    assert observed(:branch) == opaque
    assert observed(:motive) == opaque
    assert observed(:scrutinee) == opaque
    assert observed(:capture) == opaque
    assert {:case, {:var, 0}, _, _} = observed(:open)
    assert {:case, {:app, {:var, 0}, {:atom_lit, :payload}}, _, _} = observed(:spine)
  end

  test "actual nested residuals remain recorded even outside the bounded component" do
    assert {:case, {:case, _, _, _}, _, _} = observed(:nested_scrutinee)
    assert {:case, _, _, [{:"Boundary#Pack", 2, {:case, _, _, _}}]} = observed(:nested_branch)
  end

  defp observed(key) do
    {^key, program, env, depth} = Enum.find(ProofNeutralCaseFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), depth, ProofSnapshotFixture.environment())
  end
end
