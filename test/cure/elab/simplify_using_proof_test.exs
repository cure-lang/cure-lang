defmodule Cure.Elab.SimplifyUsingProofTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  test "bare using is parsed distinctly from a bracketed rule list" do
    parse = fn expression ->
      source = "proof chain\n  x == x\n  because #{expression}\n"
      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
      ast
    end

    assert {:proof_chain, _, [_, {:proof_step, _, [_, _, {:simplify_command, proof_meta, [_]}]}]} =
             parse.("simplify using evidence")

    assert proof_meta[:using] == :proof

    assert {:proof_chain, _, [_, {:proof_step, _, [_, _, {:simplify_command, rules_meta, [_]}]}]} =
             parse.("simplify using [evidence]")

    assert rules_meta[:using] == :rules
  end

  test "definitionally near evidence adapts directly to the current goal" do
    source = """
    mod AdaptNear
      type Nat = Z | S(Nat)
      fn identity(n: Nat) -> Nat = n
      fn given(x: Nat) -> Equivalent(Nat, identity(x), x) = reflexive(x)
      fn adapted(x: Nat) -> Equivalent(Nat, x, x) = proof chain
        x == x
        because simplify using given(x)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :adapted))
  end

  test "reverse endpoints are bridged with checked symmetry" do
    source = """
    mod AdaptReverse
      type Nat = Z | S(Nat)
      fn reverse(x: Nat, y: Nat, equality: Equivalent(Nat, x, y)) -> Equivalent(Nat, y, x) = proof chain
        y == x
        because simplify using equality
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :reverse))
  end

  test "local facts and nested chains can supply adaptable evidence" do
    source = """
    mod AdaptNested
      type Nat = Z | S(Nat)
      fn nested(x: Nat) -> Equivalent(Nat, x, x) = proof chain
        x == x
        because
          have prior: Equivalent(Nat, x, x) = proof chain
            x == x
            because reflexive(x)
          simplify using prior
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :nested))
  end

  test "generated equation evidence can be adapted" do
    source = """
    mod AdaptEquation
      type Nat = Z | S(Nat)
      fn identity(n: Nat) -> Nat = match n
        Z -> Z
        S(previous) -> S(previous)
      fn adapted(x: Nat) -> Equivalent(Nat, identity(S(x)), S(x)) = proof chain
        identity(S(x)) == S(x)
        because simplify using identity.S
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :adapted))
  end

  test "mismatch, wrong carrier, and non-equality evidence report E112 directly" do
    fixtures = [
      {"mismatch", "equality: Equivalent(Nat, x, y)", "x == S(y)", "equality"},
      {"wrong_carrier", "equality: Equivalent(Bool, true, true)", "x == x", "equality"},
      {"not_equality", "value: Nat", "x == x", "value"}
    ]

    for {name, parameter, proposition, evidence} <- fixtures do
      source = """
      mod AdaptFailure#{name}
        type Nat = Z | S(Nat)
        fn bad(x: Nat, y: Nat, #{parameter}) -> Equivalent(Nat, x, x) = proof chain
          #{proposition}
          because simplify using #{evidence}
      end
      """

      assert {:error,
              {:source_context,
               {:simplification_failed,
                %Cure.Diagnostic.SimplificationProblem{
                  kind: :proof_mismatch,
                  simplified_goal: simplified_goal
                } = problem}, _context}} = Program.elaborate(source)

      assert simplified_goal
      assert problem.command
      assert problem.rule
      refute inspect(problem.cause) =~ "E093"

      if problem.simplified_supplied do
        assert problem.supplied_surface =~ "Equivalent"
        assert problem.simplified_supplied_surface =~ "Equivalent"
      end
    end
  end
end
