defmodule Cure.Elab.ProofGoalTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Validator}
  alias Cure.Elab.{Erase, Program}

  defp module_source(body) do
    body = body |> String.trim() |> String.replace("\n", "\n    ")

    """
    mod ProofGoalFixture
      use Std.Equivalent
      fn proof(x: Int) -> Equivalent(Int, x, x) = #{body}
    end
    """
  end

  test "have facts extend the goal scope and lower to nested Core lets" do
    source =
      module_source("""
      proof chain
        x
          == x
          because
            have first: Equivalent(Int, x, x) = reflexive(x)
            have second: Equivalent(Int, x, x) = first
            second
      """)

    assert {:ok, env} = Program.elaborate(source)
    body = env |> Env.get_def(:proof) |> Map.fetch!(:body)
    assert Enum.count(Validator.nodes(body), &match?({:let, _, _, _, _}, &1)) == 2
  end

  test "fact shadowing is lexical inside a justification" do
    source =
      module_source("""
      proof chain
        x
          == x
          because
            have fact: Equivalent(Int, x, x) = reflexive(x)
            have fact: Equivalent(Int, x, x) = fact
            fact
      """)

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a nested proof chain can close an outer because block" do
    source =
      module_source("""
      proof chain
        x
          == x
          because
            proof chain
              x
                == x
                because reflexive(x)
      """)

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "block and inline evidence erase identically" do
    inline = module_source("proof chain\n    x\n      == x\n      because reflexive(x)")

    block =
      module_source("""
      proof chain
        x
          == x
          because
            have fact: Equivalent(Int, x, x) = reflexive(x)
            fact
      """)

    assert {:ok, inline_env} = Program.elaborate(inline)
    assert {:ok, block_env} = Program.elaborate(block)
    inline_core = inline_env |> Env.get_def(:proof) |> Map.fetch!(:body)
    block_core = block_env |> Env.get_def(:proof) |> Map.fetch!(:body)

    assert Erase.erase(inline_env, inline_core) == Erase.erase(block_env, block_core)
  end

  test "an open block reports unfinished justification with its fact inventory" do
    source =
      module_source("""
      proof chain
        x
          == x
          because
            have fact: Equivalent(Int, x, x) = reflexive(x)
      """)

    assert {:error,
            {:source_context,
             {:proof_chain_mismatch,
              %Cure.Diagnostic.ProofChainMismatchProblem{
                kind: :unfinished_justification,
                cause: {:open_goal, ["fact"]}
              }}, _context}} = Program.elaborate(source)
  end

  test "a statement after closing evidence is unreachable" do
    source =
      module_source("""
      proof chain
        x
          == x
          because
            reflexive(x)
            reflexive(x)
      """)

    assert {:error,
            {:source_context,
             {:proof_chain_syntax, %Cure.Diagnostic.ProofChainSyntaxProblem{kind: :unreachable_proof_statement}},
             _context}} =
             Program.elaborate(source)
  end

  test "directed rewrite commands transform and close forward and backward goals" do
    source = """
    mod DirectedRewrite
      use Std.Equivalent

      fn forward(x: Int, y: Int, equality: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
        x
          == y
          because
            rewrite using equality
            reflexive(y)

      fn backward(x: Int, y: Int, equality: Equivalent(Int, x, y)) -> Equivalent(Int, y, x) = proof chain
        y
          == x
          because
            rewrite backwards using equality
            reflexive(x)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "at selects one stable left-to-right occurrence" do
    source = """
    mod SelectedRewrite
      use Std.Equivalent

      fn selected(x: Int, y: Int, equality: Equivalent(Int, x, y)) -> Equivalent(Int, x, x) = proof chain
        x
          == x
          because
            rewrite using equality at 2
            equality
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "in creates a refined, shadowing local proof binding" do
    source = """
    mod HypothesisRewrite
      use Std.Equivalent

      fn refined(x: Int, y: Int, z: Int, equality: Equivalent(Int, x, y), hypothesis: Equivalent(Int, x, z)) -> Equivalent(Int, y, z) = proof chain
        y
          == z
          because
            rewrite using equality in hypothesis
            hypothesis
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end
end
