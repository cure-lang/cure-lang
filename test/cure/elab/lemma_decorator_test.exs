defmodule Cure.Elab.LemmaDecoratorTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.Env

  test "a @lemma-tagged theorem is filed under its conclusion head" do
    source = """
    mod LemmaReg
      use Std.Proof.Math

      @lemma
      fn my_positivity_fact({left: Nat}, {right: Nat},
            lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
        multiplying_positive_numbers_is_positive(lp, rp)
    end
    """

    {:ok, env} = Program.elaborate(source)

    heads = Map.keys(env.lemmas)
    ispos = Enum.find(heads, fn h -> Atom.to_string(h) |> String.ends_with?("IsPositive") end)
    assert ispos != nil, "expected a lemma filed under an IsPositive head, got: #{inspect(heads)}"

    entries = Env.lemmas(env, ispos)

    assert Enum.any?(entries, fn e ->
             Atom.to_string(e.name) |> String.ends_with?("my_positivity_fact")
           end)
  end

  test "an untagged theorem is NOT registered" do
    source = """
    mod NoLemmaReg
      use Std.Proof.Math

      fn my_positivity_fact({left: Nat}, {right: Nat},
            lp: IsPositive(left), rp: IsPositive(right)) -> IsPositive(multiply(left, right)) =
        multiplying_positive_numbers_is_positive(lp, rp)
    end
    """

    {:ok, env} = Program.elaborate(source)
    all_entries = env.lemmas |> Map.values() |> List.flatten()

    refute Enum.any?(all_entries, fn e ->
             Atom.to_string(e.name) |> String.ends_with?("my_positivity_fact")
           end)
  end
end
