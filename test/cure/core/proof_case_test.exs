defmodule Cure.Core.ProofCaseTest do
  @moduledoc """
  Fixed observation regressions, not universal Eval/model correspondence.
  Agda separately checks exact-frame model reduction and conditional safety.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.ProofCaseFixture

  @root Path.expand("../../..", __DIR__)

  test "the case observation artifact is reproducible" do
    assert {:ok, generated} = ProofCaseFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableCase.agda")
  end

  test "heterogeneous fields and caller slots keep their distinct positions" do
    grade = Grade.unrestricted()
    assert observed(:last) == {:atom_lit, :payload}
    assert observed(:first) == {:atom_type}
    assert observed(:outer) == {:atom_lit, :hidden}
    assert {:lam, ^grade, {:atom_type}, {:atom_lit, :payload}} = observed(:nested)
    assert {:lam, ^grade, {:atom_type}, {:atom_lit, :hidden}} = observed(:nested_outer)
  end

  test "actual lookup takes the first match without evaluating unused motives or branches" do
    assert observed(:duplicate) == observed(:first)
    assert observed(:skipped) == observed(:last)
    assert observed(:inert_motive) == observed(:last)
    assert observed(:redex) == observed(:last)
  end

  test "actual parameter filtering and erased padding are outside the exact model" do
    assert observed(:filtered) == {:atom_lit, :payload}
    assert observed(:erased) == {:atom_lit, :payload}
  end

  defp observed(key) do
    {^key, program, env} = Enum.find(ProofCaseFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), 0)
  end
end
