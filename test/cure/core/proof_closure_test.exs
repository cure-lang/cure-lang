defmodule Cure.Core.ProofClosureTest do
  @moduledoc """
  Reviewed finite observations only, not an arbitrary-program evaluator API
  or a theorem about all Elixir Eval/Quote executions.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Quote}
  alias Cure.Test.ProofClosureFixture

  @artifact Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableClosure.agda"

  test "all reviewed closure observations reproduce the literal Agda artifact" do
    assert {:ok, generated} = ProofClosureFixture.to_agda()
    assert generated == File.read!(@artifact)
  end

  test "a returned closure retains the actual captured argument and unnormalized body" do
    {:capture, program, environment, depth, _goal} =
      Enum.find(ProofClosureFixture.cases(), &(elem(&1, 0) == :capture))

    value = Eval.eval(program, environment)

    assert {:vlam, _, {:vatom_type},
            {:closure, [{:vatom, :payload}], {:app, {:lam, _, {:atom_type}, {:var, 0}}, {:var, 1}}}} = value

    assert {:lam, _, {:atom_type}, {:atom_lit, :payload}} = Quote.reify(value, depth)
  end

  test "higher-order application, eager arguments and lets reach the reviewed payload" do
    for key <- [:beta, :argument, :higher, :let] do
      {^key, program, environment, _depth, _goal} =
        Enum.find(ProofClosureFixture.cases(), &(elem(&1, 0) == key))

      assert {:vatom, :payload} = Eval.eval(program, environment)
    end
  end

  test "evaluation ignores let annotation without asserting native admission" do
    {:annotation, program, environment, _depth, _goal} =
      Enum.find(ProofClosureFixture.cases(), &(elem(&1, 0) == :annotation))

    assert {:let, _grade, {:hole, "payload"}, _value, _body} = program
    assert {:vatom, :payload} = Eval.eval(program, environment)
  end

  test "signature-free globals and applications of bound neutrals remain neutral" do
    {:global, program, environment, _depth, _goal} =
      Enum.find(ProofClosureFixture.cases(), &(elem(&1, 0) == :global))

    assert {:vneutral, {:nglobal, :"Boundary#answer"}} = Eval.eval(program, environment)

    {:neutral, program, environment, depth, _goal} =
      Enum.find(ProofClosureFixture.cases(), &(elem(&1, 0) == :neutral))

    assert {:vneutral, {:napp, {:nvar, 0}, {:vatom, :payload}}} = Eval.eval(program, environment)
    assert {:app, {:var, 0}, {:atom_lit, :payload}} = Quote.reify(Eval.eval(program, environment), depth)
  end
end
