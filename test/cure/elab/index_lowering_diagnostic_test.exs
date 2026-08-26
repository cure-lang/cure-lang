defmodule Cure.Elab.IndexLoweringDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Core.Env
  alias Cure.Diagnostic.{Renderer, Span}
  alias Cure.Elab.{Declarations, Program}
  alias Cure.MetaAST.SourceInfo

  test "a fractional numeric index points at its complete authored spelling" do
    source = "mod M\n  use Std.Bounded\n  fn f(x: Bounded(1.5e0)) -> Int = 1\nend\n"
    assert {:error, {:non_integer_index, details} = reason} = Program.elaborate(source, file: "fractional.cure")
    assert details.value == "1.5"

    {diagnostic, registry} = Errors.to_diagnostic(reason, "fractional.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- DEPENDENT INDEX MUST BE A WHOLE NUMBER [E093] --------------- fractional.cure

             `1.5` is fractional, but a numeric dependent index denotes a natural number.
             Fractional values cannot identify a constructor position or bounded size.

             at fractional.cure:3:19
             3 |   fn f(x: Bounded(1.5e0)) -> Int = 1
               |                   ^^^^^ this index is not a whole number

             Hint: Use a non-negative integer index, or change the indexed family to carry a different numeric type
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(2, 18, 23)
  end

  test "an unsupported operator keeps the operator expression range and suggests a total function" do
    source = "Z + Z\n"
    ast = {:binary_op, meta("operator.cure", 0, 5, operator: :+), [variable("Z"), variable("Z")]}

    assert {:error, {:unsupported_index_operator, details} = reason} =
             Declarations.lower_type(ast, [], Env.empty())

    assert details.operator == :+
    {diagnostic, registry} = Errors.to_diagnostic(reason, "operator.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- `+` IS NOT SUPPORTED DIRECTLY IN AN INDEX [E093] -------------- operator.cure

             The index lowerer recognizes comparisons and boolean connectives directly, but
             `+` has no unambiguous type-level builtin in this position.

             at operator.cure:1:1
             1 | Z + Z
               | ^^^^^ this operator has no direct index lowering

             Hint: Define the computation as a total function and call it from the index instead
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == range(0, 0, 5)
  end

  test "unsupported index forms retain structured, span-safe diagnostics" do
    cases = [
      {:unsupported_index_literal, {:literal, meta("literal.cure", 0, 4, subtype: :symbol), :tag},
       "Literal cannot be used as a dependent index"},
      {:unsupported_index_expr, {:list, meta("expression.cure", 0, 3), []},
       "Expression cannot be lowered as a dependent index"},
      {:sigma_projection_needs_ctx, {:attribute_access, meta("projection.cure", 0, 3, attribute: "1"), [variable("p")]},
       "Tuple projection lacks a checking context"}
    ]

    for {kind, ast, title} <- cases do
      assert {:error, {^kind, details} = reason} = Declarations.lower_type(ast, [], Env.empty())
      assert %Span{} = details.span

      {diagnostic, registry} = Errors.to_diagnostic(reason, details.span.path, source_for(kind))
      assert diagnostic.code == "E093"
      assert diagnostic.title == title
      assert diagnostic.primary.span == details.span
      assert diagnostic.suggestions != []
      assert Renderer.lsp(diagnostic, registry)["range"] == range(0, 0, details.span.end_byte)
      refute inspect(diagnostic.payload) =~ "source_info"
    end
  end

  test "a malformed indexed-constructor result has dedicated boundary wording" do
    span = span("result.cure", 0, 6)

    {diagnostic, _registry} =
      Errors.to_diagnostic(
        {:bad_result_type, %{family: :Vector, shape: :tuple_type, span: span}},
        "result.cure",
        "(A, B)\n"
      )

    assert diagnostic.title == "Constructor result does not name its indexed family"
    assert diagnostic.primary.span == span
    assert hd(diagnostic.suggestions).message =~ "Vector(...)"
  end

  defp source_for(:unsupported_index_literal), do: ":tag\n"
  defp source_for(:unsupported_index_expr), do: "[x]\n"
  defp source_for(:sigma_projection_needs_ctx), do: "p.1\n"

  defp variable(name), do: {:variable, [], name}

  defp meta(path, start_byte, end_byte, extra \\ []) do
    Keyword.put(extra, :source_info, %SourceInfo{whole: span(path, start_byte, end_byte)})
  end

  defp span(path, start_byte, end_byte) do
    %Span{
      source_id: path,
      path: path,
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: 1,
      start_column: start_byte + 1,
      end_line: 1,
      end_column: end_byte + 1
    }
  end

  defp range(line, start_character, end_character) do
    %{
      "start" => %{"line" => line, "character" => start_character},
      "end" => %{"line" => line, "character" => end_character}
    }
  end
end
