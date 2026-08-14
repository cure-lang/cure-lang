defmodule Cure.Diagnostic.Renderer do
  @moduledoc "Human and machine renderers for the shared diagnostic model."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Snippet, SourceRegistry, Span, Suggestion, TextEdit}

  @default_width 80

  @spec plain(Diagnostic.t(), SourceRegistry.t() | nil, keyword()) :: String.t()
  def plain(diagnostic, registry \\ nil, opts \\ [])

  def plain(%Diagnostic{} = diagnostic, opts, []) when is_list(opts),
    do: plain(diagnostic, nil, opts)

  def plain(%Diagnostic{} = diagnostic, registry, opts) do
    opts = Keyword.put_new(opts, :width, @default_width)
    diagnostic |> report_doc(registry, opts) |> Doc.plain(opts)
  end

  @spec terminal(Diagnostic.t(), SourceRegistry.t() | nil, keyword()) :: String.t()
  def terminal(diagnostic, registry \\ nil, opts \\ [])

  def terminal(%Diagnostic{} = diagnostic, opts, []) when is_list(opts),
    do: terminal(diagnostic, nil, opts)

  def terminal(%Diagnostic{} = diagnostic, registry, opts) do
    opts = Keyword.put_new_lazy(opts, :width, fn -> terminal_width(opts) end)
    document = report_doc(diagnostic, registry, opts)

    if color_enabled?(Keyword.get(opts, :color, :auto), opts),
      do: Doc.ansi(document, opts),
      else: Doc.plain(document, opts)
  end

  defp report_doc(%Diagnostic{} = diagnostic, registry, opts) do
    notes = Enum.map(diagnostic.notes, &Doc.note/1)
    suggestions = Enum.map(diagnostic.suggestions, &Doc.hint(&1.message))

    body =
      Doc.stack([
        diagnostic.body,
        evidence_doc(diagnostic, registry, opts),
        Doc.stack(notes),
        Doc.stack(suggestions),
        provenance_doc(diagnostic.provenance)
      ])

    Doc.stack([Doc.emphasis(:banner, heading(diagnostic, opts)), body])
  end

  defp evidence_doc(%Diagnostic{} = diagnostic, %SourceRegistry{} = registry, opts) do
    diagnostic.primary
    |> Snippet.plan(diagnostic.secondary, registry, opts)
    |> Snippet.to_doc(diagnostic.severity, opts)
  end

  defp evidence_doc(%Diagnostic{} = diagnostic, nil, opts), do: location_doc(diagnostic.primary, opts)

  defp heading(%Diagnostic{} = diagnostic, opts) do
    width = Keyword.fetch!(opts, :width)
    prefix = "-- #{String.upcase(diagnostic.title)} [#{diagnostic.code}] "
    path = diagnostic.primary && normalize_path(diagnostic.primary.span.path, opts)
    suffix = if path in [nil, ""], do: "", else: " " <> path
    fill = max(2, width - Doc.display_width(prefix) - Doc.display_width(suffix))
    prefix <> String.duplicate("-", fill) <> suffix
  end

  @spec to_map(Diagnostic.t()) :: map()
  def to_map(%Diagnostic{} = diagnostic) do
    %{
      "code" => diagnostic.code,
      "key" => Atom.to_string(diagnostic.key),
      "severity" => Atom.to_string(diagnostic.severity),
      "title" => diagnostic.title,
      "message" => Diagnostic.message(diagnostic),
      "body" => Doc.to_map(diagnostic.body),
      "primary" => label_map(diagnostic.primary),
      "secondary" => Enum.map(diagnostic.secondary, &label_map/1),
      "notes" => Enum.map(diagnostic.notes, &Doc.to_map/1),
      "suggestions" => Enum.map(diagnostic.suggestions, &suggestion_map/1),
      "provenance" => Enum.map(diagnostic.provenance, &provenance_map/1),
      "payload" => stringify_keys(diagnostic.payload)
    }
  end

  @spec json(Diagnostic.t()) :: String.t()
  def json(%Diagnostic{} = diagnostic), do: Jason.encode!(to_map(diagnostic))

  @doc "Project a Cure diagnostic into Elixir's compiler diagnostic envelope."
  @spec code_diagnostic(Diagnostic.t()) :: Code.diagnostic(Diagnostic.severity())
  def code_diagnostic(%Diagnostic{} = diagnostic) do
    span = primary_span(diagnostic)

    %{
      severity: diagnostic.severity,
      message: "[#{diagnostic.code}] #{diagnostic.title}\n\n#{Diagnostic.message(diagnostic)}",
      source: authored_source_path(diagnostic) || path(span),
      file: path(span),
      position: start_position(span),
      span: end_position(span),
      stacktrace: Map.get(diagnostic.payload, :stacktrace, []),
      details: diagnostic
    }
  end

  @doc "Project a Cure diagnostic into the JSON-safe form of the compiler envelope."
  @spec code_map(Diagnostic.t()) :: map()
  def code_map(%Diagnostic{} = diagnostic) do
    code_diagnostic(diagnostic)
    |> Map.put(:code, diagnostic.code)
    |> Map.put(:details, to_map(diagnostic))
    |> stringify_keys()
  end

  @doc "Project a Cure diagnostic into the standard Mix compiler structure."
  @spec mix_diagnostic(Diagnostic.t()) :: Mix.Task.Compiler.Diagnostic.t()
  def mix_diagnostic(%Diagnostic{} = diagnostic) do
    diagnostic
    |> code_diagnostic()
    |> Map.put(:compiler_name, "Cure")
    |> then(&struct!(Mix.Task.Compiler.Diagnostic, &1))
  end

  @doc "Recover the lossless Cure value carried by a host diagnostic."
  @spec from_host_diagnostic(map()) :: {:ok, Diagnostic.t()} | :error
  def from_host_diagnostic(%{details: %Diagnostic{} = diagnostic}), do: {:ok, diagnostic}
  def from_host_diagnostic(_diagnostic), do: :error

  @spec lsp(Diagnostic.t(), SourceRegistry.t() | nil, :utf8 | :utf16 | :utf32) :: map()
  def lsp(%Diagnostic{} = diagnostic, registry \\ nil, encoding \\ :utf16) do
    range = if diagnostic.primary, do: %{"range" => lsp_range(diagnostic.primary, registry, encoding)}, else: %{}

    related_information =
      diagnostic.secondary
      |> Enum.map(&related_information(&1, registry, encoding))
      |> Kernel.++(provenance_related_information(diagnostic, registry, encoding))
      |> Enum.uniq_by(fn related ->
        {get_in(related, ["location", "uri"]), get_in(related, ["location", "range"]), related["message"]}
      end)

    Map.merge(range, %{
      "severity" => lsp_severity(diagnostic.severity),
      "code" => diagnostic.code,
      "source" => "cure",
      "message" => diagnostic.title <> "\n\n" <> Diagnostic.message(diagnostic),
      "relatedInformation" => related_information,
      "data" => %{
        "key" => Atom.to_string(diagnostic.key),
        "suggestions" => Enum.map(diagnostic.suggestions, &lsp_suggestion_map(&1, registry, encoding)),
        "provenance" => Enum.map(diagnostic.provenance, &provenance_map/1),
        "payload" => stringify_keys(diagnostic.payload)
      }
    })
  end

  defp location_doc(nil, _opts), do: Doc.empty()

  defp location_doc(%Label{span: span}, opts) do
    path = normalize_path(span.path, opts) || inspect(span.source_id)
    Doc.paragraph("at #{path}:#{span.start_line}:#{span.start_column}")
  end

  defp provenance_doc([]), do: Doc.empty()

  defp provenance_doc(frames) do
    chain = Enum.map_join(frames, " -> ", &to_string(&1.name))
    Doc.paragraph("expansion: " <> chain)
  end

  defp normalize_path(nil, _opts), do: nil

  defp normalize_path(path, opts) do
    case Keyword.get(opts, :project_root) do
      nil -> path
      root -> Path.relative_to(Path.expand(path), Path.expand(root))
    end
  end

  defp terminal_width(opts) do
    device = Keyword.get(opts, :output_device, Keyword.get(opts, :device, :standard_io))

    case :io.columns(device) do
      {:ok, columns} when columns > 0 -> columns
      _ -> @default_width
    end
  end

  defp color_enabled?(value, _opts) when value in [true, :always], do: true
  defp color_enabled?(value, _opts) when value in [false, :never], do: false

  defp color_enabled?(:auto, opts) do
    device = Keyword.get(opts, :output_device, Keyword.get(opts, :device, :standard_io))
    is_nil(System.get_env("NO_COLOR")) and IO.ANSI.enabled?() and match?({:ok, _}, :io.columns(device))
  end

  defp label_map(nil), do: nil

  defp label_map(%Label{span: span, message: message, style: style}) do
    %{"span" => span_map(span), "message" => message, "style" => Atom.to_string(style)}
  end

  defp span_map(%Span{} = span) do
    span
    |> Map.from_struct()
    |> stringify_keys()
  end

  defp suggestion_map(%Suggestion{} = suggestion) do
    %{
      "message" => suggestion.message,
      "applicability" => Atom.to_string(suggestion.applicability),
      "edits" => Enum.map(suggestion.edits, &edit_map/1)
    }
  end

  defp lsp_suggestion_map(%Suggestion{} = suggestion, registry, encoding) do
    %{
      "message" => suggestion.message,
      "applicability" => Atom.to_string(suggestion.applicability),
      "edits" =>
        Enum.map(suggestion.edits, fn %TextEdit{span: span, replacement: replacement} ->
          %{
            "uri" => path_to_uri(span.path),
            "range" => lsp_range(%Label{span: span, style: :primary}, registry, encoding),
            "newText" => replacement
          }
        end)
    }
  end

  defp edit_map(%TextEdit{span: span, replacement: replacement}) do
    %{"span" => span_map(span), "replacement" => replacement}
  end

  defp provenance_map(frame) do
    %{
      "kind" => Atom.to_string(frame.kind),
      "name" => to_string(frame.name),
      "invocation" => optional_span(frame.invocation),
      "definition" => optional_span(frame.definition),
      "generated" => optional_span(frame.generated),
      "parent" => stringify_keys(frame.parent)
    }
  end

  defp optional_span(%Span{} = span), do: span_map(span)
  defp optional_span(other), do: stringify_keys(other)

  defp lsp_range(nil, _registry, _encoding),
    do: %{"start" => %{"line" => 0, "character" => 0}, "end" => %{"line" => 0, "character" => 0}}

  defp lsp_range(%Label{span: span}, %SourceRegistry{} = registry, encoding) do
    with {:ok, start_position} <- SourceRegistry.lsp_position(registry, span, :start, encoding),
         {:ok, end_position} <- SourceRegistry.lsp_position(registry, span, :end, encoding) do
      %{"start" => start_position, "end" => end_position}
    else
      _ -> lsp_range(%Label{span: span, style: :primary}, nil, encoding)
    end
  end

  defp lsp_range(%Label{span: span}, nil, _encoding) do
    %{
      "start" => %{"line" => span.start_line - 1, "character" => span.start_column - 1},
      "end" => %{"line" => span.end_line - 1, "character" => span.end_column - 1}
    }
  end

  defp related_information(%Label{span: span, message: message} = label, registry, encoding) do
    %{
      "location" => %{"uri" => path_to_uri(span.path), "range" => lsp_range(label, registry, encoding)},
      "message" => message || "related source"
    }
  end

  defp provenance_related_information(%Diagnostic{} = diagnostic, registry, encoding) do
    primary_span = primary_span(diagnostic)

    diagnostic.provenance
    |> Enum.flat_map(fn frame ->
      [
        provenance_related(frame.invocation, "`#{frame.name}` was invoked here", primary_span),
        provenance_related(frame.definition, "`#{frame.name}` is defined here", primary_span),
        provenance_related(frame.generated, "`#{frame.name}` generated this declaration", primary_span)
      ]
    end)
    |> Enum.reject(&is_nil/1)
    |> Enum.map(&related_information(&1, registry, encoding))
  end

  defp provenance_related(%Span{} = span, _message, %Span{} = primary) when span == primary, do: nil

  defp provenance_related(%Span{} = span, message, _primary),
    do: %Label{span: span, style: :secondary, message: message}

  defp provenance_related(_span, _message, _primary), do: nil

  defp primary_span(%Diagnostic{primary: %Label{span: span}}), do: span
  defp primary_span(_diagnostic), do: nil

  defp path(%Span{path: path}), do: path
  defp path(nil), do: nil

  defp start_position(%Span{} = span), do: {span.start_line, span.start_column}
  defp start_position(nil), do: 0

  defp end_position(%Span{} = span), do: {span.end_line, span.end_column}
  defp end_position(nil), do: nil

  defp authored_source_path(%Diagnostic{provenance: provenance}) do
    provenance
    |> Enum.reverse()
    |> Enum.find_value(fn frame ->
      case frame.invocation do
        %Span{path: path} -> path
        _ -> nil
      end
    end)
  end

  defp path_to_uri(nil), do: ""
  defp path_to_uri("file://" <> _ = uri), do: uri
  defp path_to_uri(path), do: "file://" <> Path.expand(path)

  defp lsp_severity(:error), do: 1
  defp lsp_severity(:warning), do: 2
  defp lsp_severity(:information), do: 3
  defp lsp_severity(:hint), do: 4

  defp stringify_keys(nil), do: nil
  defp stringify_keys(%Diagnostic{} = diagnostic), do: to_map(diagnostic)
  defp stringify_keys(%Span{} = span), do: span_map(span)

  defp stringify_keys(%{__struct__: _module} = value) do
    value |> Map.from_struct() |> stringify_keys()
  end

  defp stringify_keys(map) when is_map(map) do
    Map.new(map, fn {key, value} -> {stringify_key(key), stringify_keys(value)} end)
  end

  defp stringify_keys(list) when is_list(list), do: Enum.map(list, &stringify_keys/1)
  defp stringify_keys(tuple) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> Enum.map(&stringify_keys/1)
  defp stringify_keys(value) when is_atom(value), do: Atom.to_string(value)
  defp stringify_keys(value), do: value

  defp stringify_key(key) when is_binary(key), do: key
  defp stringify_key(key) when is_atom(key) or is_integer(key) or is_float(key), do: to_string(key)
  defp stringify_key(key), do: inspect(key, limit: :infinity, printable_limit: :infinity)
end
