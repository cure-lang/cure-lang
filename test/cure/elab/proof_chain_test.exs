defmodule Cure.Elab.ProofChainTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Validator}
  alias Cure.Elab.Program

  defp source(steps) do
    continuations =
      1..steps
      |> Enum.map(fn _ -> "\n    _ == x\n      because reflexive(x)" end)
      |> Enum.join("\n")

    """
    mod Chain#{steps}
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == x
          because reflexive(x)
    #{continuations}
    end
    """
  end

  for steps <- [1, 2, 3, 50] do
    test "elaborates and kernel-checks a chain with #{steps + 1} steps" do
      assert {:ok, env} = Program.elaborate(source(unquote(steps)))
      body = env |> Env.get_def(:proof) |> Map.fetch!(:body)

      assert Enum.all?(Validator.nodes(body), fn
               {:proof_chain, _, _} -> false
               {:proof_step, _, _} -> false
               _ -> true
             end)

      assert Enum.count(Validator.nodes(body), &match?({:global, :"Std.Equivalent#trans"}, &1)) ==
               unquote(steps)
    end
  end

  test "a wrong inline justification is rejected at its chain step" do
    source = """
    mod BadChain
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x
          == 1
          because reflexive(x)
    end
    """

    assert {:error,
            {:source_context,
             {:proof_chain_mismatch,
              %Cure.Diagnostic.ProofChainMismatchProblem{kind: :wrong_justification, step_index: 0}}, _context}} =
             Program.elaborate(source)
  end

  test "a chain is an expression and can be bound inside a larger expression" do
    source = """
    mod NestedChain
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) =
        have chained: Equivalent(Int, x, x) = proof chain
          x
            == x
            because reflexive(x)
        sym(chained)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
