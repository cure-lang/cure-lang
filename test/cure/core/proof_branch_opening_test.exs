defmodule Cure.Core.ProofBranchOpeningTest do
  @moduledoc """
  Fixed terminating branch-opening observations, not universal execution refinement.
  General scope, denotation and protected-binder laws are independently checked in Agda.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.{ProofBranchOpeningFixture, ProofDataSpineFixture}

  @root Path.expand("../../..", __DIR__)

  test "the actual opening frames and readbacks are reproducible" do
    assert {:ok, generated} = ProofBranchOpeningFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableBranchOpening.agda")
  end

  test "zero, first, last and outer slots retain their distinct indices" do
    assert observed(:zero) == {:atom_lit, :payload}
    assert observed(:one) == {:var, 0}
    assert observed(:first) == {:var, 2}
    assert observed(:last) == {:var, 0}
    assert observed(:outer) == {:var, 3}
    assert {:ctor, :"Opening#Frame", [{:var, 1}, {:var, 0}, {:var, 2}]} = observed(:spine)
  end

  test "the actual captured frame uses ascending levels reversed before the caller tail" do
    probe = {:lam, Grade.unrestricted(), {:atom_type}, {:var, 0}}

    assert {:vlam, _, _,
            {:closure,
             [
               {:vneutral, {:nvar, 3}},
               {:vneutral, {:nvar, 2}},
               {:vneutral, {:nvar, 1}},
               {:vneutral, {:nvar, 0}}
             ], _}} = Eval.open_branch([{:vneutral, {:nvar, 0}}], probe, 3, 1)
  end

  test "nested binders, data and case bodies keep capture and readback depth" do
    grade = Grade.unrestricted()
    assert {:lam, ^grade, {:atom_type}, {:atom_lit, :payload}} = observed(:closure)
    assert observed(:redex) == {:var, 1}
    assert observed(:case) == {:var, 1}
    assert observed(:data) == {:data, :"Spine#Indexed", [{:atom_type}], [{:var, 1}]}

    assert {:lam, ^grade, {:atom_type}, {:data, :"Spine#Indexed", [{:atom_type}], [{:atom_lit, :payload}]}} =
             observed(:capture)
  end

  defp observed(key) do
    {^key, depth, arity, env, body} = Enum.find(ProofBranchOpeningFixture.cases(), &(elem(&1, 0) == key))
    Quote.reify(Eval.open_branch(env, body, arity, depth), depth + arity, ProofDataSpineFixture.environment())
  end
end
