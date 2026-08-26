defmodule Cure.Diagnostic.NamedArgumentDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry, Span}

  defp span(line, first, last) do
    %Span{
      source_id: "named.cure",
      path: "named.cure",
      start_byte: first,
      end_byte: last,
      start_line: line,
      start_column: first + 1,
      end_line: line,
      end_column: last + 1
    }
  end

  test "E115 projects authored label, value, and declaration ranges through JSON and LSP" do
    label = span(3, 20, 24)
    value = span(3, 26, 27)
    parameter = span(2, 10, 11)

    diagnostic =
      Adapter.from_error(
        {:named_argument_mismatch, :unknown_label,
         %{
           label: "nope",
           written: ["nope"],
           label_spans: [label],
           argument_spans: [value],
           parameter_spans: [parameter]
         }},
        span: span(3, 15, 28)
      )

    assert diagnostic.code == "E115"
    assert diagnostic.key == :named_argument_mismatch
    assert diagnostic.primary.span == label
    assert Enum.any?(diagnostic.secondary, &(&1.span == value))
    assert Enum.any?(diagnostic.secondary, &(&1.span == parameter))

    json = diagnostic |> Renderer.json() |> Jason.decode!()
    registry = SourceRegistry.new() |> SourceRegistry.register("named.cure", "\n\n\n" <> String.duplicate("x", 40))
    lsp = Renderer.lsp(diagnostic, registry, :utf16)
    assert json["code"] == "E115"
    assert lsp["code"] == "E115"
    assert lsp["data"]["payload"]["kind"] == "unknown_label"
  end

  test "missing required name offers a machine-applicable insertion" do
    value = span(4, 30, 31)

    diagnostic =
      Adapter.from_error(
        {:named_argument_mismatch, :missing_label,
         %{label: "proof", written: nil, parameter_index: 0, argument_spans: [value]}},
        span: value
      )

    assert [%{applicability: :machine_applicable, edits: [edit]}] = diagnostic.suggestions
    assert edit.replacement == "proof: "
    assert edit.span.start_byte == edit.span.end_byte
  end
end
