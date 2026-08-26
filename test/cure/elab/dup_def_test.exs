defmodule Cure.Elab.DupDefTest do
  @moduledoc """
  A module must not define the same function name twice. Every real dependent
  language (Idris/Agda/Lean) rejects duplicate top-level definitions; Cure was
  silently keeping the last (Map.put overwrite in `Env.add_def`), so a program
  could typecheck against one body and silently run another. Reject it.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp elaborate(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    Program.check_ast(ast)
  end

  test "duplicate same-named def in one module is rejected" do
    src = """
    mod DupDef
      fn foo() -> Int = 1
      fn foo() -> Int = 2
    end
    """

    assert {:error, {:overlapping_overload, %{name: :foo, arity: 0}}} = elaborate(src)
  end

  test "distinct def names in one module still elaborate" do
    src = """
    mod NoDup
      fn foo() -> Int = 1
      fn bar() -> Int = 2
    end
    """

    assert {:ok, _env} = elaborate(src)
  end
end
