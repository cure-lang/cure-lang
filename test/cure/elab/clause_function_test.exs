defmodule Cure.Elab.ClauseFunctionTest do
  use ExUnit.Case, async: false

  @moduledoc """
  Multi-clause function-head syntax (`fn f(n) | 0 -> ... | n -> ...`) desugars to
  a `match` over the formal parameters, so the dependent pipeline accepts it the
  same way it accepts the explicit `match` body. Single-parameter clauses match
  the parameter directly; a `when` guard rides through as a match-arm guard.
  """

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
    :code.purge(mod)
  end

  test "single-parameter clauses run on the BEAM (factorial)" do
    src = """
    mod ClauseFac
      fn factorial(n: Int) -> Int
        | 0 -> 1
        | n -> n * factorial(n - 1)
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod.factorial(0) == 1
    assert mod.factorial(5) == 120
  after
    purge(:"Cure.ClauseFac")
  end

  test "literal and variable clauses fall through in order (fibonacci)" do
    src = """
    mod ClauseFib
      fn fib(n: Int) -> Int
        | 0 -> 0
        | 1 -> 1
        | n -> fib(n - 1) + fib(n - 2)
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod.fib(0) == 0
    assert mod.fib(1) == 1
    assert mod.fib(7) == 13
  after
    purge(:"Cure.ClauseFib")
  end

  test "when-guards on clauses ride through as a match-arm guard chain" do
    # A guarded match in the dependent pipeline is a guard *chain*: every guarded
    # arm's pattern must be a catch-all (variable), the same shape `pickup` lowers
    # to. The clause desugar preserves that, so a pure guard-chain function works.
    src = """
    mod ClauseGuard
      fn sign(n: Int) -> Int
        | n when n > 0 -> 1
        | n when n < 0 -> 0 - 1
        | n -> 0
    """

    assert {:ok, mod} = Cure.Compiler.compile_and_load(src, emit_events: false)
    assert mod.sign(7) == 1
    assert mod.sign(-3) == -1
    assert mod.sign(0) == 0
  after
    purge(:"Cure.ClauseGuard")
  end
end
