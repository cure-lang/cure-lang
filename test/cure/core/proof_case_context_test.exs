defmodule Cure.Core.ProofCaseContextTest do
  @moduledoc """
  Fixed producer/observation regressions, not universal kernel admission.
  Agda independently replays character fidelity, context evidence and native safety.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Eval, Grade, ProofRecipe, Quote}
  alias Cure.Test.{ProofBundleFixture, ProofCaseContextFixture}

  @root Path.expand("../../..", __DIR__)

  test "the context-aware caller artifact is reproducible" do
    assert {:ok, generated} = ProofCaseContextFixture.to_agda()
    assert generated == File.read!(@root <> "/proof/Fixtures/ExecutableCaseContext.agda")
  end

  test "existing caller tag and tuple fields suffice without native context proof data" do
    assert [_, _, _] = ProofCaseContextFixture.requests()

    for {_key, {:caller, _tele, _kinds, _args, _arg_recipes, _subject, _goal, _body, _kind} = query, _env} <-
          ProofCaseContextFixture.requests() do
      assert {:ok, chars} = ProofRecipe.encode_caller(query, ProofBundleFixture.table())
      assert String.starts_with?(chars, "(" <> String.duplicate("1", 19))
    end
  end

  test "open dependent cases, lambda cases and nested branch cases have the reviewed readbacks" do
    grade = Grade.unrestricted()

    for {key, {:caller, _tele, _kinds, _args, _arg_recipes, subject, _goal, _body, _kind}, env} <-
          ProofCaseContextFixture.requests() do
      quoted = Quote.reify(Eval.eval(subject, env), 0)

      case key do
        :lambda -> assert {:lam, ^grade, {:atom_type}, {:var, 0}} = quoted
        key when key in [:dependent, :nested] -> assert quoted == {:atom_lit, :payload}
      end
    end
  end
end
