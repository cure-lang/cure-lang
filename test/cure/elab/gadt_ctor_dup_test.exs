defmodule Cure.Elab.GadtCtorDupTest do
  @moduledoc """
  A GADT/indexed constructor's named domains bind names that later domains and the
  result index can reference (dependent constructor, e.g. `(k: Nat) -> Vec(k)`), so
  a repeated name (`(x: Nat) -> (x: Nat) -> …`) shadows and makes references
  ambiguous — the same telescope-linearity rule as function parameters.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.check_ast(ast)
  end

  test "duplicate named param in a GADT constructor is rejected" do
    src =
      "mod GC\n  type Nat = Z | S(Nat)\n  type Box indices (n: Nat)\n    mk : (x: Nat) -> (x: Nat) -> Box(Z)\nend\n"

    assert {:error, {:source_context, {:duplicate_parameter, :x}, _}} = elaborate(src)
  end

  test "distinct named params in a GADT constructor still elaborate" do
    src =
      "mod GCok\n  type Nat = Z | S(Nat)\n  type Box indices (n: Nat)\n    mk : (x: Nat) -> (y: Nat) -> Box(Z)\nend\n"

    assert {:ok, _} = elaborate(src)
  end
end
