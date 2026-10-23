defmodule Cure.Core.ProofScrutineeTest do
  @moduledoc """
  Fixed actual observation regressions, not universal Eval/model correspondence.
  Native typing and exact-case simulation are independently replayed in Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.{ProofCaseFixture, ProofScrutineeFixture}

  @root Path.expand("../../..", __DIR__)

  test "the evaluated-scrutinee artifact is reproducible" do
    assert {:ok, generated} = ProofScrutineeFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableScrutinee.agda")
  end

  test "computed and caller-variable scrutinees retain their constructor fields" do
    for key <- [:beta, :zeta, :eager, :variable, :zero] do
      assert observed(key) == {:atom_lit, :payload}
    end

    assert observed(:outer) == {:atom_lit, :hidden}
    assert {:ctor, :"Boundary#Alternate", [{:atom_type}, {:atom_lit, :payload}]} = observed(:nested)
    grade = Grade.unrestricted()
    assert {:lam, ^grade, {:atom_type}, {:atom_lit, :payload}} = observed(:capture)
  end

  test "unused motives and branches are not evaluated" do
    assert observed(:skipped) == {:atom_lit, :payload}
    assert observed(:inert_motive) == {:atom_lit, :payload}
  end

  test "actual neutral preservation and filtered layouts remain broader than the exact model" do
    neutral = {:case, {:global, :"Boundary#packed"}, {:atom_type}, [{:"Boundary#Pack", 2, {:var, 0}}]}
    assert {:vneutral, {:ncase, _head, _motive, _branches}} = Eval.eval(neutral, [])
    assert Quote.reify(Eval.eval(neutral, []), 0) == neutral

    for key <- [:filtered, :erased] do
      {^key, {:case, scrutinee, motive, branches}, []} =
        Enum.find(ProofCaseFixture.cases(), &(elem(&1, 0) == key))

      program = {:case, {:let, Grade.unrestricted(), {:atom_type}, scrutinee, {:var, 0}}, motive, branches}
      assert {:atom_lit, :payload} = Quote.reify(Eval.eval(program, []), 0)
    end
  end

  defp observed(key) do
    {^key, program, env} = Enum.find(ProofScrutineeFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.eval(program, env), 0)
  end
end
