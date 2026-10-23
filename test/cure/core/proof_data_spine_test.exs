defmodule Cure.Core.ProofDataSpineTest do
  @moduledoc """
  Fixed actual data readback regressions, not universal extraction or typing.
  Agda separately checks finite layout, field readback and native safety.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, Quote}
  alias Cure.Test.ProofDataSpineFixture

  @root Path.expand("../../..", __DIR__)

  test "the independent data snapshot, certificate and observations are reproducible" do
    assert {:ok, generated} = ProofDataSpineFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableDataSpine.agda")
  end

  test "signature-aware readback recovers parameter and dependent-index slots" do
    {program, values, quoted} = observed(:canonical)
    assert {:vdata, :"Spine#Indexed", [{:vatom_type}, {:vatom, :payload}]} = values
    assert quoted == program
    assert {:data, :"Spine#Indexed", [{:atom_type}], [{:atom_lit, :payload}]} = quoted
    assert {:data, :"Spine#Indexed", [{:atom_type}, {:atom_lit, :payload}], []} = Quote.reify(values, 0)
    assert {_, _, ^quoted} = observed(:redex)
    assert {_, _, ^quoted} = observed(:parameter)
  end

  test "field closures normalize and neutral fields keep their ambient index" do
    grade = Grade.unrestricted()

    assert {_, _,
            {:data, :"Spine#Indexed", [{:pi, ^grade, {:atom_type}, {:atom_type}}],
             [{:lam, ^grade, {:atom_type}, {:var, 0}}]}} = observed(:closure)

    assert {_, _, {:data, :"Spine#Indexed", [{:atom_type}], [{:var, 0}]}} = observed(:open)
  end

  test "ordinary splitting is not arity validation or typing" do
    assert {_, _, {:data, :"Spine#Indexed", [{:atom_type}], []}} = observed(:short)
    assert {_, _, {:data, :"Spine#Indexed", [_parameter], [_first, _second]}} = observed(:extra)
    {unknown, values, quoted} = observed(:unknown)
    refute unknown == quoted
    assert quoted == Quote.reify(values, 0)
    {forged, _, quoted} = observed(:forged)
    refute forged == quoted
    assert {_, _, ^quoted} = observed(:canonical)
    assert {_, _, {:data, :"Spine#Indexed", [{:atom_type}], [{:atom_type}]}} = observed(:ill_typed)
  end

  defp observed(key) do
    {^key, program, env, depth} = Enum.find(ProofDataSpineFixture.cases(), &(elem(&1, 0) == key))
    value = Eval.eval(program, env)
    {program, value, Quote.reify(value, depth, ProofDataSpineFixture.environment())}
  end
end
