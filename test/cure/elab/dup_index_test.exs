defmodule Cure.Elab.DupIndexTest do
  @moduledoc """
  An indexed family must not bind the same index name twice: later index types and
  each constructor's result indices reference the index binders by name, so a
  duplicate (`indices (n: Nat, n: Nat)`) makes those references ambiguous. Same
  telescope-linearity rule as function parameters.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Program.check_ast(ast)
  end

  test "duplicate family index name is rejected" do
    src =
      "mod DI\n  type Nat = Z | S(Nat)\n  type Vec indices (n: Nat, n: Nat)\n    vz : Vec(Z, Z)\nend\n"

    assert {:error, {:duplicate_index, :n}} = elaborate(src)
  end

  test "distinct index names still elaborate" do
    src =
      "mod DIok\n  type Nat = Z | S(Nat)\n  type Vec indices (n: Nat, m: Nat)\n    vz : Vec(Z, Z)\nend\n"

    assert {:ok, _} = elaborate(src)
  end
end
