defmodule Cure.Elab.NonlinearPatternTest do
  @moduledoc """
  A constructor pattern must be linear: it may not bind the same variable name
  twice (`C(x, x)`). Idris/Agda reject non-linear patterns — the body's reference
  is ambiguous, and a repeated binder is not a valid pattern (equality between two
  positions must be witnessed by a proof, not written as a repeated name). The bare
  wildcard `_` is exempt (it binds nothing).
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    case Program.check_ast(ast) do
      {:error, error} -> {:error, Program.semantic_error(error)}
      result -> result
    end
  end

  test "non-linear constructor pattern (C(x, x)) is rejected" do
    src = """
    mod NL
      type P = C(Int, Int)
      fn f(p: P) -> Int = match p
        C(x, x) -> x
    end
    """

    assert {:error, {:nonlinear_pattern, :x}} = elaborate(src)
  end

  test "distinct pattern variables still elaborate" do
    src = """
    mod NLok
      type P = C(Int, Int)
      fn f(p: P) -> Int = match p
        C(x, y) -> x
    end
    """

    assert {:ok, _} = elaborate(src)
  end

  test "repeated wildcards are allowed (bind nothing)" do
    src = """
    mod NLwild
      type P = C(Int, Int)
      fn f(p: P) -> Int = match p
        C(_, _) -> 0
    end
    """

    assert {:ok, _} = elaborate(src)
  end
end
