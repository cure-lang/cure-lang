defmodule Cure.Compiler.SolverTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.MetaAST.Metadata

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "all solver commands print and reparse" do
    for source <- ["by search", "by positivity", "by decide", "by decide using equivalent?(true, true)"] do
      assert {:solver_command, meta, _} = ast = parse!(source)
      assert meta[:solver] in [:search, :positivity, :decide]
      assert Printer.quoted_to_string(ast) == source
      assert Metadata.strip_diagnostics(parse!(Printer.quoted_to_string(ast))) == Metadata.strip_diagnostics(ast)
    end
  end

  test "solver vocabulary remains ordinary identifiers outside by-solver heads" do
    for name <- ["by", "search", "positivity", "decide"] do
      assert {:variable, _, ^name} = parse!(name)
      assert {:function_call, meta, [_]} = parse!("#{name}(true)")
      assert meta[:name] == name
    end
  end
end
