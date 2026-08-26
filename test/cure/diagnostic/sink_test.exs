defmodule Cure.Diagnostic.SinkTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Operational, Sink}

  test "collects diagnostics and renders them with shared options" do
    diagnostic = Operational.file_read("demo.cure", :enoent)
    sink = Sink.new(format: :plain, width: 72) |> Sink.emit(diagnostic)

    assert [rendered] = Sink.render_all(sink)
    assert rendered =~ "E095"
    assert rendered =~ "demo.cure"
    assert length(sink.diagnostics) == 1
  end

  test "flush writes diagnostics and clears the batch" do
    {:ok, device} = StringIO.open("")
    sink = Sink.new(format: :plain, output_device: device) |> Sink.emit(Operational.usage("cure check"))

    assert {:ok, flushed} = Sink.flush(sink)
    assert flushed.diagnostics == []
    {_input, output} = StringIO.contents(device)
    assert output =~ "E099"
  end

  test "machine formats preserve structured output" do
    diagnostic = Operational.usage("cure check")
    sink = Sink.new(format: :json) |> Sink.emit(diagnostic)
    assert [%{"code" => "E099"}] = Sink.render_all(sink)
  end

  test "LSP flush emits JSON rather than an Elixir inspection" do
    diagnostic = Operational.usage("cure check")
    {:ok, device} = StringIO.open("")
    sink = Sink.new(format: :lsp, output_device: device) |> Sink.emit(diagnostic)

    assert {:ok, _flushed} = Sink.flush(sink)
    {_input, output} = StringIO.contents(device)
    assert [%{"code" => "E099"}] = Jason.decode!(output)
  end

  test "Code flush emits structured JSON rather than an Elixir inspection" do
    diagnostic = Operational.usage("cure check")
    {:ok, device} = StringIO.open("")
    sink = Sink.new(format: :code, output_device: device) |> Sink.emit(diagnostic)

    assert {:ok, _flushed} = Sink.flush(sink)
    {_input, output} = StringIO.contents(device)
    assert [%{"code" => "E099", "severity" => "error"}] = Jason.decode!(output)
  end

  test "Code flush preserves the compiler envelope fields" do
    diagnostic =
      Cure.Diagnostic.new(
        code: "E099",
        key: :usage_error,
        severity: :error,
        title: "Invalid command usage",
        body: Cure.Diagnostic.Doc.paragraph("cure check"),
        primary: %Cure.Diagnostic.Label{
          span:
            Cure.Diagnostic.Span.new(
              source_id: :source,
              path: "demo.cure",
              start_byte: 0,
              end_byte: 1,
              start_line: 1,
              start_column: 1,
              end_line: 1,
              end_column: 2
            ),
          style: :primary
        }
      )

    {:ok, device} = StringIO.open("")
    sink = Sink.new(format: :code, output_device: device) |> Sink.emit(diagnostic)

    assert {:ok, _flushed} = Sink.flush(sink)
    {_input, output} = StringIO.contents(device)
    [rendered] = Jason.decode!(output)

    assert rendered["code"] == "E099"
    assert rendered["severity"] == "error"
    assert rendered["file"] == "demo.cure"
    assert rendered["message"] =~ "E099"
    assert rendered["details"]["code"] == "E099"
  end

  test "LSP rendering honors the configured position encoding" do
    source = "😀 value\n"
    registry = Cure.Diagnostic.SourceRegistry.new() |> Cure.Diagnostic.SourceRegistry.register(:source, source)
    {:ok, span} = Cure.Diagnostic.SourceRegistry.span(registry, :source, 5, 10)

    diagnostic =
      Cure.Diagnostic.new(
        code: "E099",
        key: :usage_error,
        severity: :error,
        title: "Usage",
        body: Cure.Diagnostic.Doc.paragraph("bad"),
        primary: %Cure.Diagnostic.Label{span: span, style: :primary}
      )

    sink = Sink.new(format: :lsp, registry: registry, position_encoding: :utf8)
    assert Sink.render(sink, diagnostic)["range"]["start"]["character"] == 5
  end

  test "LSP rendering omits a range when a diagnostic has no authored span" do
    diagnostic =
      Cure.Diagnostic.new(
        code: "E100",
        key: :artifact_error,
        severity: :error,
        title: "Invalid build artifact",
        message: "artifact is invalid"
      )

    rendered = Sink.render(Sink.new(format: :lsp), diagnostic)
    refute Map.has_key?(rendered, "range")
  end

  test "JSON normalizes nested provenance values" do
    diagnostic =
      Cure.Diagnostic.new(
        code: "E092",
        key: :macro_expansion_failed,
        severity: :error,
        title: "Macro expansion failed",
        message: "the macro could not expand",
        provenance: [
          %Cure.Diagnostic.ProvenanceFrame{
            kind: :macro_expansion,
            name: "every",
            parent: {:expansion, %{phase: :parser}}
          }
        ]
      )

    rendered = diagnostic |> Cure.Diagnostic.Renderer.json() |> Jason.decode!()

    assert rendered["provenance"] == [
             %{
               "kind" => "macro_expansion",
               "name" => "every",
               "invocation" => nil,
               "definition" => nil,
               "generated" => nil,
               "parent" => ["expansion", %{"phase" => "parser"}]
             }
           ]
  end

  test "LSP exposes cross-file macro provenance as related source locations" do
    registry =
      Cure.Diagnostic.SourceRegistry.new()
      |> Cure.Diagnostic.SourceRegistry.register(:use, "fn run() = build 1\n", "/project/use.cure")
      |> Cure.Diagnostic.SourceRegistry.register(
        :definition,
        "syntax build <x: Code> becomes x\n",
        "/project/macros.cure"
      )
      |> Cure.Diagnostic.SourceRegistry.register(:generated, "fn run() = bad\n", "/project/generated.cure")

    {:ok, invocation} = Cure.Diagnostic.SourceRegistry.span(registry, :use, 11, 18)
    {:ok, definition} = Cure.Diagnostic.SourceRegistry.span(registry, :definition, 0, 32)
    {:ok, generated} = Cure.Diagnostic.SourceRegistry.span(registry, :generated, 11, 14)

    diagnostic =
      Cure.Diagnostic.new(
        code: "E092",
        key: :macro_expansion_failed,
        severity: :error,
        title: "Macro expansion failed",
        message: "generated code is invalid",
        primary: %Cure.Diagnostic.Label{span: generated, style: :primary},
        provenance: [
          %Cure.Diagnostic.ProvenanceFrame{
            kind: :macro_expansion,
            name: "build",
            invocation: invocation,
            definition: definition,
            generated: generated
          }
        ]
      )

    rendered = Cure.Diagnostic.Renderer.lsp(diagnostic, registry, :utf16)

    assert Enum.map(rendered["relatedInformation"], fn related ->
             {related["message"], related["location"]["uri"], related["location"]["range"]}
           end) == [
             {"`build` was invoked here", "file:///project/use.cure",
              %{
                "start" => %{"line" => 0, "character" => 11},
                "end" => %{"line" => 0, "character" => 18}
              }},
             {"`build` is defined here", "file:///project/macros.cure",
              %{
                "start" => %{"line" => 0, "character" => 0},
                "end" => %{"line" => 0, "character" => 32}
              }}
           ]
  end
end
