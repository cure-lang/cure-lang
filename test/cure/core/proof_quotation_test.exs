defmodule Cure.Core.ProofQuotationTest do
  @moduledoc """
  Reviewed terminating Quote observations, not an arbitrary normalization
  service or universal implementation theorem. Agda validates model replay.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Quote}
  alias Cure.Test.ProofQuotationFixture

  @artifact Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableQuotation.agda"

  test "the deeper readback artifact is reproducible" do
    assert {:ok, generated} = ProofQuotationFixture.to_agda()
    assert generated == File.read!(@artifact)
  end

  test "dependent binders preserve levels while reducing their bodies" do
    {:dependent, program, env, depth, _goal} =
      Enum.find(ProofQuotationFixture.cases(), &(elem(&1, 0) == :dependent))

    assert {:lam, _, {:type, 0}, {:lam, _, {:var, 0}, {:var, 0}}} =
             Quote.reify(Eval.eval(program, env), depth)
  end

  test "quotation normalizes a Pi-valued domain before returning syntax" do
    {:domain, program, env, depth, _goal} =
      Enum.find(ProofQuotationFixture.cases(), &(elem(&1, 0) == :domain))

    assert {:lam, _, {:pi, _, {:atom_type}, {:atom_type}}, {:var, 0}} =
             Quote.reify(Eval.eval(program, env), depth)
  end

  test "a neutral spine quotes its lambda argument without eta contraction" do
    {:argument, program, env, depth, _goal} =
      Enum.find(ProofQuotationFixture.cases(), &(elem(&1, 0) == :argument))

    assert {:app, {:var, 0}, {:lam, _, {:atom_type}, {:var, 0}}} =
             Quote.reify(Eval.eval(program, env), depth)

    {:eta, program, env, depth, _goal} =
      Enum.find(ProofQuotationFixture.cases(), &(elem(&1, 0) == :eta))

    assert {:lam, _, {:atom_type}, {:app, {:var, 1}, {:var, 0}}} =
             Quote.reify(Eval.eval(program, env), depth)
  end

  test "signature-free quotation retains a global under the binder" do
    {:global, program, env, depth, _goal} =
      Enum.find(ProofQuotationFixture.cases(), &(elem(&1, 0) == :global))

    assert {:lam, _, {:atom_type}, {:global, :"Boundary#answer"}} =
             Quote.reify(Eval.eval(program, env), depth)
  end
end
