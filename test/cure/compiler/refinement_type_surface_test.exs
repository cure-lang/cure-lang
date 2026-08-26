defmodule Cure.Compiler.RefinementTypeSurfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer}

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  test "proof-backed refinement syntax parses and prints losslessly" do
    source = """
    mod RefinementSurface
      type PositiveNatural = {value: Nat | IsPositive(value)}
    end
    """

    ast = parse!(source)
    {:block, _, [{:container, _, [{:type_annotation, _, [{:refinement_type, refinement_meta, _}]} | _]} | _]} = ast

    assert %Cure.MetaAST.SourceInfo{
             whole: %Cure.Diagnostic.Span{},
             name: %Cure.Diagnostic.Span{},
             annotation: %Cure.Diagnostic.Span{},
             body: %Cure.Diagnostic.Span{},
             opener: %Cure.Diagnostic.Span{},
             closer: %Cure.Diagnostic.Span{}
           } = Keyword.fetch!(refinement_meta, :source_info)

    printed = Printer.quoted_to_string(ast)
    assert printed =~ "{value: Nat | IsPositive(value)}"
    reparsed = parse!(printed)
    assert Printer.quoted_to_string(reparsed) == printed
  end
end
