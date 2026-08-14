defmodule Cure.Compiler.Errors do
  @moduledoc """
  Formats compiler errors into human-readable messages with source locations.

  Handles errors from every pipeline stage: lexer, parser, type checker,
  and code generation.

  ## Example output

      error: type mismatch in function 'bad'
       --> hello.cure:3
        | declared return type Int but body has type String
  """

  @doc """
  Format a compiler error into a human-readable string.

  Accepts error tuples from any pipeline stage and a file path for context.
  """
  @spec format_error(term(), String.t()) :: String.t()
  def format_error(error, file \\ "nofile")

  def format_error(%Cure.Diagnostic{} = diagnostic, file) do
    body = Cure.Diagnostic.message(diagnostic)

    extras =
      (Enum.map(diagnostic.notes, &Cure.Diagnostic.Doc.plain(&1, width: 1_000_000)) ++
         Enum.map(diagnostic.suggestions, & &1.message))
      |> Enum.join(" ")

    body = [body, extras] |> Enum.reject(&(&1 == "")) |> Enum.join(" ") |> String.replace(~r/\s+/, " ")

    location =
      case {diagnostic.primary, diagnostic.payload} do
        {%Cure.Diagnostic.Label{span: %{start_line: line}}, _} when is_integer(line) and line > 0 ->
          "#{file}:#{line}"

        {_, %{line: line}} when is_integer(line) and line > 0 ->
          "#{file}:#{line}"

        _ ->
          file
      end

    "-- #{String.upcase(diagnostic.title)} [#{diagnostic.code}]\n--> #{location}\n#{body}"
  end

  def format_error(errors, file) when is_list(errors) do
    Enum.map_join(errors, "\n\n", &format_error(&1, file))
  end

  def format_error({:type_error, errors}, file) when is_list(errors) do
    format_error(errors, file)
  end

  def format_error({:parse_error, errors}, file) when is_list(errors) do
    format_error(errors, file)
  end

  def format_error({:file_read_error, path, reason}, _file) do
    Cure.Diagnostic.Operational.from_error({:file_read_error, path, reason})
    |> format_error(path)
  end

  def format_error(error, file) do
    error
    |> structured_for_format()
    |> format_error(file)
  end

  defp structured_for_format({:expected_module, _ast}),
    do: Cure.Diagnostic.Adapter.from_error({:expected_module, nil})

  defp structured_for_format({:codegen_error, {:computed_macro_error, _meta, _reason} = error}),
    do: Cure.Diagnostic.Adapter.from_error(error)

  defp structured_for_format(error), do: Cure.Diagnostic.Adapter.from_error(error)

  # -- "Did you mean?" Suggestions ---------------------------------------------

  # -- Error Catalog ------------------------------------------------------------

  @doc """
  Look up an error code explanation.

  Returns `{:ok, text}` or `:error` if the code is unknown.
  """
  @spec explain(String.t()) :: {:ok, String.t()} | :error
  def explain(code), do: Cure.Diagnostic.Registry.explain(code)

  @doc """
  Return all known error codes with a one-line summary each.

  Each element is `{code, title, brief}` where `title` is the short name
  (e.g. "Type Mismatch") and `brief` is the first descriptive sentence.
  The list is sorted by code.
  """
  @spec list_all() :: [{String.t(), String.t(), String.t()}]
  def list_all, do: Cure.Diagnostic.Registry.list_all()

  @doc false
  @spec catalog_explanation!(String.t()) :: String.t()
  def catalog_explanation!(code), do: Cure.Diagnostic.Registry.catalog_explanation!(code)

  @doc false
  @spec catalog_entries() :: [{String.t(), String.t(), String.t()}]
  def catalog_entries, do: Cure.Diagnostic.Registry.catalog_entries()

  @doc """
  Suggest similar names for typos using the shared, case-insensitive restricted
  Damerau-Levenshtein distance.

  Both `name` and every entry in `candidates` are coerced to strings
  before comparison. Atoms are converted via `Atom.to_string/1`; any
  other shape (including `nil`) is dropped from the candidate list and
  causes `nil` to be returned when it appears as the `name`. This
  defends against atom keys leaking out of the type-environment scope
  maps (e.g. the lexer keyword `:else`), which would otherwise crash
  `String.length/1` deep inside the Levenshtein loop.
  """
  @spec suggest(term(), [term()]) :: String.t() | nil
  def suggest(name, candidates) do
    case to_string_safe(name) do
      nil ->
        nil

      name_str ->
        candidates
        |> Enum.map(&to_string_safe/1)
        |> Enum.filter(&is_binary/1)
        |> Enum.map(fn candidate ->
          {candidate, Cure.Diagnostic.Suggest.distance(name_str, candidate)}
        end)
        |> Enum.filter(fn {_, d} -> d > 0 and d <= 2 end)
        |> Enum.sort_by(fn {candidate, distance} ->
          {distance, String.downcase(candidate), candidate}
        end)
        |> case do
          [{best, _} | _] -> best
          _ -> nil
        end
    end
  end

  # Best-effort coercion to a binary; returns `nil` for anything that
  # cannot be sensibly displayed as text.
  defp to_string_safe(value) when is_binary(value), do: value
  defp to_string_safe(value) when is_atom(value) and not is_nil(value), do: Atom.to_string(value)
  defp to_string_safe(_), do: nil

  @doc """
  Format an error with source context showing the offending line.
  """
  @spec format_with_source(term(), String.t(), String.t()) :: String.t()
  def format_with_source(error, file, source) do
    {diagnostic, registry} = to_diagnostic(error, file, source)

    Cure.Diagnostic.Sink.new(format: :plain, registry: registry)
    |> Cure.Diagnostic.Sink.render(diagnostic)
  end

  @doc "Convert an error at the compiler presentation boundary."
  @spec to_diagnostic(term(), String.t(), String.t()) ::
          {Cure.Diagnostic.t(), Cure.Diagnostic.SourceRegistry.t()}
  def to_diagnostic(error, file, source), do: to_diagnostic(error, file, source, [])

  @doc "Convert an error with presentation options such as `debug: true`."
  @spec to_diagnostic(term(), String.t(), String.t(), keyword()) ::
          {Cure.Diagnostic.t(), Cure.Diagnostic.SourceRegistry.t()}
  def to_diagnostic(error, file, source, presentation_opts) do
    # The source identity is the same identity carried by lexer/parser spans.
    # Keeping it stable lets unsaved LSP buffers and generated source registries
    # resolve exact UTF-8/16/32 positions without a scalar-column fallback.
    source_id = file

    registry =
      Cure.Diagnostic.SourceRegistry.new()
      |> Cure.Diagnostic.SourceRegistry.register(source_id, source, file)
      |> register_embedded_sources(error)

    opts =
      case exact_error_span(error, source, source_id, registry) do
        {:ok, span} -> [span: span]
        _ -> []
      end

    opts =
      case branch_patterns(error) do
        [] -> opts
        patterns -> Keyword.put(opts, :branch_patterns, remap_branch_patterns(patterns, registry, source_id))
      end

    opts =
      if Keyword.get(presentation_opts, :debug, false),
        do: Keyword.put(opts, :debug, true),
        else: opts

    # The presentation boundary always knows the authored file even when an
    # error has no usable span. Internal diagnostics must not lose that context
    # merely because the failing pipeline stage could not attach a label.
    opts = opts |> Keyword.put(:source_file, file) |> Keyword.put(:source_registry, registry)

    diagnostic =
      if operational_error?(error) do
        Cure.Diagnostic.Operational.from_error(error)
      else
        Cure.Diagnostic.Adapter.from_error(error, opts)
      end

    diagnostic =
      if operational_error?(error) do
        remap_operational_span(diagnostic, registry, source_id)
      else
        diagnostic
      end

    # `compile_string/2` intentionally uses `nofile` unless its caller supplies
    # a file.  This presentation boundary does have the caller's source identity,
    # so carry it through every user-visible range rather than leaving labels and
    # edits attached to an unregistered source.
    diagnostic = remap_diagnostic_spans(diagnostic, registry, source_id)

    {diagnostic, registry}
  end

  defp register_embedded_sources(registry, error) do
    error
    |> embedded_sources()
    |> Enum.reduce(registry, fn {source_id, source, path}, registry ->
      Cure.Diagnostic.SourceRegistry.register(registry, source_id, source, path)
    end)
  end

  defp embedded_sources(%{source: source, file: file}) when is_binary(source) and is_binary(file),
    do: [{file, source, file}]

  defp embedded_sources(%_{} = struct), do: struct |> Map.from_struct() |> embedded_sources()

  defp embedded_sources(map) when is_map(map) do
    map
    |> Map.values()
    |> Enum.flat_map(&embedded_sources/1)
  end

  defp embedded_sources(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.flat_map(&embedded_sources/1)

  defp embedded_sources(list) when is_list(list), do: Enum.flat_map(list, &embedded_sources/1)
  defp embedded_sources(_term), do: []

  defp remap_diagnostic_spans(%Cure.Diagnostic{} = diagnostic, registry, source_id) do
    remap_term_spans(diagnostic, registry, source_id)
  end

  defp remap_term_spans(%Cure.Diagnostic.Span{source_id: existing} = span, registry, source_id)
       when existing in [nil, "nofile"] or existing == source_id do
    case Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte) do
      {:ok, remapped} -> remapped
      {:error, _} -> span
    end
  end

  defp remap_term_spans(%Cure.Diagnostic.Span{} = span, _registry, _source_id), do: span

  defp remap_term_spans(term, registry, source_id) when is_list(term) do
    Enum.map(term, &remap_term_spans(&1, registry, source_id))
  end

  defp remap_term_spans(term, registry, source_id) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.map(&remap_term_spans(&1, registry, source_id))
    |> List.to_tuple()
  end

  defp remap_term_spans(term, registry, source_id) when is_map(term) do
    term
    |> Map.to_list()
    |> Enum.reduce(term, fn {key, value}, remapped ->
      Map.put(remapped, key, remap_term_spans(value, registry, source_id))
    end)
  end

  defp remap_term_spans(term, _registry, _source_id), do: term

  defp remap_operational_span(
         %Cure.Diagnostic{
           primary: %Cure.Diagnostic.Label{span: %Cure.Diagnostic.Span{source_id: source_id}}
         } = diagnostic,
         _registry,
         source_id
       ),
       do: diagnostic

  defp remap_operational_span(
         %Cure.Diagnostic{primary: %Cure.Diagnostic.Label{span: %Cure.Diagnostic.Span{} = span} = label} =
           diagnostic,
         registry,
         source_id
       ) do
    case Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte) do
      {:ok, remapped} -> %{diagnostic | primary: %{label | span: remapped}}
      {:error, _} -> diagnostic
    end
  end

  defp remap_operational_span(
         %Cure.Diagnostic{primary: nil, payload: %{line: line} = payload} = diagnostic,
         registry,
         source_id
       )
       when is_integer(line) and line > 0 do
    column = Map.get(payload, :column, 1)

    case Cure.Diagnostic.SourceRegistry.span_at(registry, source_id, line, column, 0) do
      {:ok, span} ->
        label = %Cure.Diagnostic.Label{
          span: span,
          style: :primary,
          message: operational_location_message(payload)
        }

        %{diagnostic | primary: label}

      {:error, _} ->
        diagnostic
    end
  end

  defp remap_operational_span(diagnostic, _registry, _source_id), do: diagnostic

  defp operational_location_message(%{rule: rule}), do: "rule #{rule} applies here"
  defp operational_location_message(_payload), do: "warning applies here"

  defp branch_patterns({:source_context, _reason, context}) when is_map(context),
    do: Map.get(context, :branch_patterns, [])

  defp branch_patterns(_error), do: []

  defp remap_branch_patterns(patterns, registry, source_id) do
    Enum.map(patterns, fn
      %{span: %Cure.Diagnostic.Span{} = span} = pattern ->
        case Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte) do
          {:ok, remapped} -> %{pattern | span: remapped}
          {:error, _} -> pattern
        end

      pattern ->
        pattern
    end)
  end

  defp operational_error?({:file_read_error, _, _}), do: true
  defp operational_error?({:file_write_error, _, _}), do: true
  defp operational_error?({:dependency_resolution_failed, _}), do: true
  defp operational_error?({:command_failed, _, _}), do: true
  defp operational_error?({:migration_warning, details}) when is_map(details), do: true
  defp operational_error?({:compiler_warning, details}) when is_map(details), do: true
  defp operational_error?({:export_unmappable, _}), do: true
  defp operational_error?({:snap_missing, _}), do: true
  defp operational_error?({:configuration_warning, _}), do: true
  defp operational_error?({:usage_error, _}), do: true
  defp operational_error?({:artifact_error, _}), do: true
  defp operational_error?({:proof_file_missing, _}), do: true
  defp operational_error?({:proof_verification_failed, _}), do: true
  defp operational_error?({:proof_schema_incompatible, _}), do: true
  defp operational_error?({:snap_schema_incompatible, _}), do: true
  defp operational_error?({:registry_signature_invalid, _}), do: true
  defp operational_error?({:transparency_log_unreachable, _}), do: true
  defp operational_error?({:registry_fetch_failed, _}), do: true
  defp operational_error?({:registry_hash_mismatch, _}), do: true
  defp operational_error?({:registry_package_not_found, _}), do: true
  defp operational_error?({:version_conflict, _, _}), do: true
  defp operational_error?({:invalid_dependency, _}), do: true
  defp operational_error?({:invalid_constraint, _, _}), do: true
  defp operational_error?({:no_versions, _}), do: true
  defp operational_error?({:dependency_clone_failed, _, _}), do: true
  defp operational_error?({:dependency_edition_error, _, _}), do: true
  defp operational_error?({:unknown_watch_action, _}), do: true
  defp operational_error?({:file_error, _}), do: true
  defp operational_error?({:decode_failed, _}), do: true
  defp operational_error?({:parse, _}), do: true
  defp operational_error?({:fetch_failed, _, _}), do: true
  defp operational_error?({:hash_mismatch, _}), do: true
  defp operational_error?({:package_not_found, _}), do: true
  defp operational_error?({:unreachable, _}), do: true
  defp operational_error?({:chain_broken, _}), do: true
  defp operational_error?({:app_resource_write_failed, _, _}), do: true
  defp operational_error?({:write_failed, _, _}), do: true
  defp operational_error?({:load_failed, _}), do: true
  defp operational_error?({:compilation_failed, _}), do: true
  defp operational_error?({:duplicate_app, _}), do: true
  defp operational_error?({:app_name_mismatch, _, _}), do: true
  defp operational_error?({:compile_failed, _}), do: true
  defp operational_error?({:release_build_failed, _}), do: true
  defp operational_error?({:release_app_missing, _, _}), do: true
  defp operational_error?({:sys_config_read_failed, _, _}), do: true
  defp operational_error?({:vm_args_read_failed, _, _}), do: true
  defp operational_error?({:undocumented_public_function, _, _}), do: true
  defp operational_error?(_), do: false

  defp error_location({:lift_module_error, %{source_provenance: %{line: line, col: col}}}), do: {line, col}
  defp error_location({:lex_error, reason}), do: lex_error_location(reason)
  defp error_location({_, _, meta}) when is_list(meta), do: {Keyword.get(meta, :line, 0), Keyword.get(meta, :col, 0)}

  defp error_location({:computed_macro_error, meta, _reason}) when is_list(meta) do
    {Keyword.get(meta, :line, 0), Keyword.get(meta, :col, Keyword.get(meta, :column, 0))}
  end

  defp error_location({kind, line, col})
       when kind in [:edition_pragma_placement, :edition_pragma_malformed, :edition_pragma_unknown] and
              is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location({:parse_error, [reason | _]}), do: error_location(reason)
  defp error_location({:codegen_error, reason}), do: error_location(reason)

  defp error_location({:source_context, _reason, %{line: line, column: col}})
       when is_integer(line) and is_integer(col),
       do: {line, col}

  defp error_location(_error), do: {0, 0}

  defp span_contains_position?(%Cure.Diagnostic.Span{} = span, line, column) do
    cond do
      line < span.start_line or line > span.end_line ->
        false

      line == span.start_line and column < span.start_column ->
        false

      line == span.end_line and column > span.end_column ->
        false

      true ->
        true
    end
  end

  # Parser recovery can return several independent errors as a bare list.
  # Search each item for the first honest source span so presentation callers
  # do not lose the file/caret merely because the parser accumulated errors.
  defp exact_error_span([reason | rest], source, source_id, registry) do
    case exact_error_span(reason, source, source_id, registry) do
      {:ok, span} -> {:ok, span}
      :error -> exact_error_span(rest, source, source_id, registry)
    end
  end

  defp exact_error_span([], _source, _source_id, _registry), do: :error

  defp exact_error_span(error, source, source_id, registry) do
    case hole_span(error, source) do
      {:ok, start_byte, end_byte} ->
        Cure.Diagnostic.SourceRegistry.span(registry, source_id, start_byte, end_byte)

      :error ->
        exact_error_span_without_hole(error, source, source_id, registry)
    end
  end

  defp exact_error_span_without_hole(error, source, source_id, registry) do
    if insertion_at_eof?(error) do
      ending = source |> String.replace(~r/(?:\r\n|\r|\n)+\z/, "") |> byte_size()
      Cure.Diagnostic.SourceRegistry.span(registry, source_id, ending, ending)
    else
      case embedded_span(error) do
        %Cure.Diagnostic.Span{} = span ->
          Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte)

        nil ->
          token_span_at_error(error, source, source_id, registry)
      end
    end
  end

  defp hole_span({:codegen_error, reason}, source), do: hole_span(reason, source)

  # Real compiler producers carry the parser-owned token range all the way to
  # the presentation boundary. Prefer it to searching the source, which can
  # select a hole-looking comment or a different authored hole.
  defp hole_span(
         {:unfilled_hole, %{span: %Cure.Diagnostic.Span{start_byte: start_byte, end_byte: end_byte}}},
         _source
       ),
       do: {:ok, start_byte, end_byte}

  defp hole_span(_error, _source), do: :error

  defp insertion_at_eof?({:lex_error, {kind, _line, _column}})
       when kind in [:unterminated_string, :unterminated_char, :unterminated_quoted_identifier],
       do: true

  defp insertion_at_eof?({:parse_error, [reason | _]}), do: insertion_at_eof?(reason)
  defp insertion_at_eof?(_error), do: false

  defp token_span_at_error(error, source, source_id, registry) do
    case error_location(error) do
      {line, col} when line > 0 and col > 0 ->
        token =
          with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: "diagnostic", emit_events: false) do
            Enum.find(tokens, fn
              %Cure.Compiler.Token{span: %Cure.Diagnostic.Span{} = span} ->
                span_contains_position?(span, line, col)

              _ ->
                false
            end)
          else
            _ -> nil
          end

        case token do
          %Cure.Compiler.Token{span: %Cure.Diagnostic.Span{} = span} ->
            Cure.Diagnostic.SourceRegistry.span(registry, source_id, span.start_byte, span.end_byte)

          nil ->
            case Cure.Diagnostic.SourceRegistry.span_at(registry, source_id, line, col, 0) do
              {:ok, span} -> {:ok, span}
              {:error, _} -> :error
            end
        end

      _ ->
        :error
    end
  end

  defp embedded_span({:parse_error, [reason | _]}), do: embedded_span(reason)
  defp embedded_span({:codegen_error, reason}), do: embedded_span(reason)
  defp embedded_span({:expected, _, :got, _, _, _, %Cure.Diagnostic.Span{} = span}), do: span
  defp embedded_span({:expected_token, _, _, _, _, _, %Cure.Diagnostic.Span{} = span}), do: span
  defp embedded_span({:source_context, {:proof_chain_mismatch, _} = reason, _context}), do: embedded_span(reason)
  defp embedded_span({:source_context, {:proof_chain_syntax, _} = reason, _context}), do: embedded_span(reason)
  defp embedded_span({:source_context, {:rewrite_failed, _} = reason, _context}), do: embedded_span(reason)
  defp embedded_span({:source_context, {:simplification_failed, _} = reason, _context}), do: embedded_span(reason)

  defp embedded_span({:source_context, {:defining_equation_unavailable, _} = reason, _context}),
    do: embedded_span(reason)

  defp embedded_span({:source_context, _reason, %{span: %Cure.Diagnostic.Span{} = span}}), do: span

  defp embedded_span({:proof_chain_syntax, %Cure.Diagnostic.ProofChainSyntaxProblem{} = problem}),
    do: problem.step || problem.construct || problem.insertion

  defp embedded_span({:proof_chain_mismatch, %Cure.Diagnostic.ProofChainMismatchProblem{} = problem}),
    do: problem.justification || problem.current_step

  defp embedded_span({:rewrite_failed, %Cure.Diagnostic.RewriteProblem{} = problem}),
    do: problem.command || problem.theorem || problem.goal

  defp embedded_span({:simplification_failed, %Cure.Diagnostic.SimplificationProblem{} = problem}),
    do: problem.command || problem.rule

  defp embedded_span({:defining_equation_unavailable, %Cure.Diagnostic.DefiningEquationProblem{} = problem}),
    do: problem.equation_use || problem.function_definition

  defp embedded_span({:source_context, reason, _context}), do: embedded_span(reason)
  defp embedded_span({_kind, %{span: %Cure.Diagnostic.Span{} = span}}), do: span
  defp embedded_span(_error), do: nil

  defp lex_error_location(reason) when is_tuple(reason) do
    case reason |> Tuple.to_list() |> Enum.reverse() do
      [col, line | _] when is_integer(line) and is_integer(col) -> {line, col}
      _ -> {0, 0}
    end
  end

  defp lex_error_location(_reason), do: {0, 0}
end
