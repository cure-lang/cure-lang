defmodule Cure.Refactor.Rewrite.Result do
  @moduledoc "Result of a structural Cure module split."

  @enforce_keys [
    :source_path,
    :target_path,
    :source_module,
    :target_module,
    :selected,
    :source,
    :target,
    :added_imports,
    :applied?
  ]
  defstruct [
    :source_path,
    :target_path,
    :source_module,
    :target_module,
    :selected,
    :source,
    :target,
    :added_imports,
    :applied?
  ]

  @type t :: %__MODULE__{
          source_path: Path.t(),
          target_path: Path.t(),
          source_module: String.t(),
          target_module: String.t(),
          selected: [String.t()],
          source: String.t(),
          target: String.t(),
          added_imports: [String.t()],
          applied?: boolean()
        }
end

defmodule Cure.Refactor.Rewrite do
  @moduledoc """
  Machine-applicable, AST-selected source rewrites for Cure modules.

  The first operation is a top-level module split, modelled after Rhizoid's
  `--split`. Selectors are resolved from the parsed declaration records; source
  bytes are only sliced at parser-provided declaration spans. No declaration is
  located by a regular expression or line-number guess.

  Cure module names are part of canonical definition identity, so a split must
  name the destination module explicitly. A split specification has the form
  `Target.cure:Target.Module:Declaration|OtherDeclaration`.

  The generated source is reparsed before it can be written. Dependency edges
  crossing the split are retained with a generated `use` import. Private
  declarations crossing that boundary are rejected because a `use` cannot make
  a private definition public. The API is dry-run by default; pass `write: true`
  to apply the already-verified pair of source buffers.
  """

  alias Cure.Compiler.{Lexer, Parser, Trivia}
  alias Cure.Diagnostic.Span
  alias Cure.Refactor.Analysis
  alias Cure.Refactor.Analysis.Declaration

  @type split_spec :: %{
          required(:target_file) => String.t(),
          required(:target_module) => String.t(),
          required(:selectors) => [String.t()]
        }

  @type error ::
          {:invalid_split_spec, String.t()}
          | {:file_read_error, Path.t(), atom()}
          | {:analysis_error, term()}
          | {:source_changed, Path.t()}
          | {:selection_error, String.t()}
          | {:dependency_error, String.t()}
          | {:target_exists, Path.t()}
          | {:write_error, Path.t(), atom()}
          | {:generated_parse_error, Path.t(), [term()]}
          | {:generated_module_error, Path.t(), String.t()}
          | term()

  @doc "Parse a Rhizoid-style Cure split specification."
  @spec parse_spec(String.t()) :: {:ok, split_spec()} | {:error, error()}
  def parse_spec(spec) when is_binary(spec) do
    case String.split(spec, ":", parts: 3) do
      [target_file, target_module, selector_text]
      when target_file != "" and target_module != "" and selector_text != "" ->
        selectors = String.split(selector_text, "|", trim: true)

        if Path.extname(target_file) != ".cure" do
          {:error, {:invalid_split_spec, "target file must end in `.cure`: #{target_file}"}}
        else
          case selectors do
            [] -> {:error, {:invalid_split_spec, "split must select at least one declaration"}}
            _ -> {:ok, %{target_file: target_file, target_module: target_module, selectors: selectors}}
          end
        end

      _ ->
        {:error, {:invalid_split_spec, "expected `Target.cure:Target.Module:Declaration|OtherDeclaration`"}}
    end
  end

  def parse_spec(_spec), do: {:error, {:invalid_split_spec, "split specification must be a string"}}

  @doc """
  Plan and optionally apply one structural top-level split.

  `write: false` (the default) returns both generated buffers without touching
  the filesystem. `write: true` writes the destination and modified source only
  after both buffers have passed the lexer/parser round-trip check.
  """
  @spec split(Path.t(), split_spec() | String.t(), keyword()) :: {:ok, Result.t()} | {:error, error()}
  def split(source_path, spec, opts \\ []) do
    with {:ok, spec} <- normalize_spec(spec),
         {:ok, source} <- read_source(source_path),
         {:ok, report} <- analyze(source_path),
         :ok <- ensure_source_unchanged(source, report),
         {:ok, selected} <- select_declarations(report, spec.selectors),
         :ok <- ensure_movable(selected, Keyword.get(opts, :remove_from_source, true)),
         {:ok, crossing} <- dependency_edges(report.declarations, selected),
         :ok <- ensure_boundary_acyclic(crossing, selected, Keyword.get(opts, :remove_from_source, true)),
         {:ok, target_path} <- target_path(source_path, spec.target_file, opts),
         :ok <- ensure_target_is_distinct(source_path, target_path),
         :ok <- ensure_target_available(target_path, opts),
         {:ok, generated} <-
           generate(
             source,
             report,
             selected,
             crossing,
             spec,
             source_path,
             target_path,
             Keyword.get(opts, :remove_from_source, true)
           ),
         :ok <- verify_generated(generated.source_module, generated.source, generated.source_path),
         :ok <- verify_generated(generated.target_module, generated.target, generated.target_path),
         {:ok, applied?} <- maybe_write(generated, opts) do
      {:ok,
       %Cure.Refactor.Rewrite.Result{
         source_path: source_path,
         target_path: target_path,
         source_module: report.module,
         target_module: spec.target_module,
         selected: Enum.map(selected, & &1.name),
         source: generated.source,
         target: generated.target,
         added_imports: generated.added_imports,
         applied?: applied?
       }}
    end
  end

  @doc "Return a compact JSON-safe summary of a rewrite result."
  @spec to_map(Cure.Refactor.Rewrite.Result.t()) :: map()
  def to_map(%Cure.Refactor.Rewrite.Result{} = result) do
    %{
      source_path: result.source_path,
      target_path: result.target_path,
      source_module: result.source_module,
      target_module: result.target_module,
      selected: result.selected,
      added_imports: result.added_imports,
      applied: result.applied?
    }
  end

  @doc """
  Add a structural public re-export to an existing module.

  This is the compatibility half of a split: callers that already `use` the
  source module continue to see declarations moved to the destination module.
  The edit is inserted at the parsed import boundary and is reparsed before it
  can be written.
  """
  @spec ensure_public_use(Path.t(), String.t(), keyword()) ::
          {:ok, %{source: String.t(), added?: boolean()}} | {:error, error()}
  def ensure_public_use(source_path, target_module, opts \\ [])

  def ensure_public_use(source_path, target_module, opts) when is_binary(target_module) do
    with {:ok, source} <- read_source(source_path),
         {:ok, report} <- analyze(source_path),
         :ok <- ensure_source_unchanged(source, report) do
      if has_import?(report, target_module) do
        {:ok, %{source: source, added?: false}}
      else
        rewritten = insert_imports(source, report, ["public use #{target_module}"])

        with :ok <- verify_generated(report.module, rewritten, source_path),
             :ok <- maybe_write_source(source_path, rewritten, opts) do
          {:ok, %{source: rewritten, added?: true}}
        end
      end
    end
  end

  def ensure_public_use(_source_path, _target_module, _opts),
    do: {:error, {:invalid_split_spec, "re-export target module must be a string"}}

  @doc "Add an ordinary structural `use` import to a module."
  @spec ensure_use(Path.t(), String.t(), keyword()) ::
          {:ok, %{source: String.t(), added?: boolean()}} | {:error, error()}
  def ensure_use(source_path, target_module, opts \\ [])

  def ensure_use(source_path, target_module, opts) when is_binary(target_module) do
    with {:ok, source} <- read_source(source_path),
         {:ok, report} <- analyze(source_path),
         :ok <- ensure_source_unchanged(source, report) do
      if has_import?(report, target_module) do
        {:ok, %{source: source, added?: false}}
      else
        rewritten = insert_imports(source, report, ["use #{target_module}"])

        with :ok <- verify_generated(report.module, rewritten, source_path),
             :ok <- maybe_write_source(source_path, rewritten, opts) do
          {:ok, %{source: rewritten, added?: true}}
        end
      end
    end
  end

  def ensure_use(_source_path, _target_module, _opts),
    do: {:error, {:invalid_split_spec, "import target module must be a string"}}

  @doc "Remove ordinary structural `use` imports for a module."
  @spec remove_use(Path.t(), String.t(), keyword()) ::
          {:ok, %{source: String.t(), removed?: boolean()}} | {:error, error()}
  def remove_use(source_path, target_module, opts \\ [])

  def remove_use(source_path, target_module, opts) when is_binary(target_module) do
    with {:ok, source} <- read_source(source_path),
         {:ok, report} <- analyze(source_path),
         :ok <- ensure_source_unchanged(source, report) do
      imports =
        report.imports
        |> Enum.filter(fn import ->
          import.source == target_module and import.import_type == "use" and not import.public
        end)

      if imports == [] do
        {:ok, %{source: source, removed?: false}}
      else
        rewritten =
          imports
          |> Enum.map(&span_from_map(&1.span))
          |> Enum.reject(&is_nil/1)
          |> remove_import_spans(source)

        with :ok <- verify_generated(report.module, rewritten, source_path),
             :ok <- maybe_write_source(source_path, rewritten, opts) do
          {:ok, %{source: rewritten, removed?: true}}
        end
      end
    end
  end

  def remove_use(_source_path, _target_module, _opts),
    do: {:error, {:invalid_split_spec, "import target module must be a string"}}

  @doc "Normalize a source file to one trailing newline through the structural rewrite path."
  @spec normalize_trailing_newline(Path.t(), keyword()) ::
          {:ok, %{source: String.t(), changed?: boolean()}} | {:error, error()}
  def normalize_trailing_newline(source_path, opts \\ []) do
    with {:ok, source} <- read_source(source_path),
         {:ok, report} <- analyze(source_path),
         :ok <- ensure_source_unchanged(source, report) do
      rewritten = String.trim_trailing(source, "\n") <> "\n"

      with :ok <- verify_generated(report.module, rewritten, source_path),
           :ok <- maybe_write_source(source_path, rewritten, opts) do
        {:ok, %{source: rewritten, changed?: rewritten != source}}
      end
    end
  end

  defp normalize_spec(spec) when is_map(spec) do
    with {:ok, target_file} <- nonempty_string(spec[:target_file], :target_file),
         {:ok, target_module} <- nonempty_string(spec[:target_module], :target_module),
         {:ok, selectors} <- selectors(spec[:selectors]),
         :ok <- validate_target_file(target_file) do
      {:ok, %{target_file: target_file, target_module: target_module, selectors: selectors}}
    end
  end

  defp normalize_spec(spec), do: parse_spec(spec)

  defp nonempty_string(value, _key) when is_binary(value) and value != "", do: {:ok, value}
  defp nonempty_string(_value, key), do: {:error, {:invalid_split_spec, "#{key} must be a non-empty string"}}

  defp selectors(values) when is_list(values) do
    values = Enum.filter(values, &(is_binary(&1) and &1 != ""))

    if values == [],
      do: {:error, {:invalid_split_spec, "split must select at least one declaration"}},
      else: {:ok, values}
  end

  defp selectors(_values), do: {:error, {:invalid_split_spec, "selectors must be a list"}}

  defp validate_target_file(target_file) do
    if Path.extname(target_file) == ".cure",
      do: :ok,
      else: {:error, {:invalid_split_spec, "target file must end in `.cure`: #{target_file}"}}
  end

  defp read_source(path) do
    case File.read(path) do
      {:ok, source} -> {:ok, source}
      {:error, reason} -> {:error, {:file_read_error, path, reason}}
    end
  end

  defp analyze(path) do
    case Analysis.analyze(path, dependencies: true) do
      {:ok, report} -> {:ok, report}
      {:error, reason} -> {:error, {:analysis_error, reason}}
    end
  end

  defp ensure_source_unchanged(source, report) do
    digest = :sha256 |> :crypto.hash(source) |> Base.encode16(case: :lower)
    if digest == report.source_hash, do: :ok, else: {:error, {:source_changed, report.path}}
  end

  defp select_declarations(report, selectors) do
    top_level = Enum.filter(report.declarations, &(&1.depth == 0))

    selected =
      Enum.filter(top_level, fn declaration ->
        Enum.any?(selectors, &selector_matches?(&1, declaration, report.module))
      end)

    selected_names = MapSet.new(Enum.map(selected, &selector_key(&1, report.module)))

    missing =
      selectors
      |> Enum.reject(fn selector ->
        Enum.any?(selected, &selector_matches?(selector, &1, report.module))
      end)

    cond do
      missing != [] ->
        {:error, {:selection_error, "no top-level declaration matches: #{Enum.join(missing, ", ")}"}}

      MapSet.size(selected_names) != length(selected) ->
        {:error, {:selection_error, "a declaration was selected more than once"}}

      true ->
        if Enum.any?(selected, &is_nil(&1.span)),
          do: {:error, {:selection_error, "selected declaration has no source span"}},
          else: {:ok, Enum.sort_by(selected, & &1.source_order)}
    end
  end

  defp selector_matches?(selector, %Declaration{name: name, identity: identity}, module) do
    selector == name or selector == to_string(identity) or selector == "#{module}##{name}"
  end

  defp selector_key(%Declaration{identity: identity, name: name}, module),
    do: to_string(identity || "#{module}##{name}")

  defp dependency_edges(declarations, selected) do
    selected_keys = MapSet.new(Enum.map(selected, & &1.identity))
    declarations_by_id = Map.new(declarations, &{&1.identity, &1})

    {selected_to_remaining, remaining_to_selected} =
      Enum.reduce(declarations, {[], []}, fn declaration, {out, back} ->
        declaration_selected? = MapSet.member?(selected_keys, declaration.identity)

        Enum.reduce(declaration.references, {out, back}, fn reference, {out, back} ->
          target_selected? = MapSet.member?(selected_keys, reference.identity)

          cond do
            declaration_selected? and not target_selected? and
                Map.has_key?(declarations_by_id, reference.identity) ->
              {[{declaration, reference} | out], back}

            not declaration_selected? and target_selected? ->
              {out, [{declaration, reference} | back]}

            true ->
              {out, back}
          end
        end)
      end)

    crossing = %{selected_to_remaining: selected_to_remaining, remaining_to_selected: remaining_to_selected}

    case private_crossing(crossing, declarations_by_id) do
      [] -> {:ok, crossing}
      names -> {:error, {:dependency_error, "private declarations cross the split boundary: #{Enum.join(names, ", ")}"}}
    end
  end

  defp ensure_movable(selected, true) do
    private =
      selected
      |> Enum.filter(fn declaration ->
        declaration.kind in [:function, :macro] and declaration.visibility not in [nil, :public]
      end)
      |> Enum.map(& &1.name)

    if private == [],
      do: :ok,
      else: {:error, {:dependency_error, "private declarations cannot be moved: #{Enum.join(private, ", ")}"}}
  end

  defp ensure_movable(_selected, false), do: :ok

  defp ensure_boundary_acyclic(%{selected_to_remaining: [_ | _]}, selected, true) do
    if public_declarations?(selected) do
      {:error,
       {:dependency_error,
        "selected declarations depend on declarations left in the source; select that dependency closure to keep the split acyclic"}}
    else
      :ok
    end
  end

  defp ensure_boundary_acyclic(_crossing, _selected, _remove_from_source), do: :ok

  defp private_crossing(%{selected_to_remaining: selected, remaining_to_selected: remaining}, declarations_by_id) do
    (selected ++ remaining)
    |> Enum.flat_map(fn {_declaration, reference} ->
      case Map.get(declarations_by_id, reference.identity) do
        %Declaration{kind: kind, visibility: visibility, name: name}
        when kind in [:function, :macro] and visibility not in [nil, :public] ->
          [name]

        _ ->
          []
      end
    end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp target_path(source_path, target_file, opts) do
    output_directory = Keyword.get(opts, :output_directory, Path.dirname(source_path))
    {:ok, Path.expand(Path.join(output_directory, target_file))}
  end

  defp ensure_target_is_distinct(source_path, target_path) do
    if Path.expand(source_path) == target_path,
      do: {:error, {:invalid_split_spec, "target file must differ from source file"}},
      else: :ok
  end

  defp ensure_target_available(path, opts) do
    if Keyword.get(opts, :write, false) and File.exists?(path) and not Keyword.get(opts, :overwrite, false),
      do: {:error, {:target_exists, path}},
      else: :ok
  end

  defp generate(source, report, selected, crossing, spec, source_path, target_path, remove_from_source?) do
    selected_spans = Enum.map(selected, & &1.span)
    source_without_selected = if remove_from_source?, do: remove_spans(source, selected_spans), else: source
    source_module = report.module
    target_import = "public use #{spec.target_module}"

    source_needs_import? =
      remove_from_source? and public_declarations?(selected) and
        not has_import?(report, spec.target_module)

    target_needs_import? = crossing.selected_to_remaining != [] and not has_import?(report, source_module)
    source_imports = if source_needs_import?, do: [target_import], else: []
    target_imports = if target_needs_import?, do: ["use #{source_module}"], else: []
    source_with_import = insert_imports(source_without_selected, report, source_imports)
    target = build_target(source, report, selected, target_imports, spec.target_module, source_path)

    {:ok,
     %{
       source_module: source_module,
       target_module: spec.target_module,
       source: source_with_import,
       target: target,
       target_path: target_path,
       source_path: source_path,
       added_imports: source_imports ++ target_imports
     }}
  end

  defp has_import?(report, module) do
    Enum.any?(report.imports, &(&1.source == module))
  end

  defp public_declarations?(declarations) do
    Enum.all?(declarations, fn declaration ->
      declaration.kind not in [:function, :macro] or declaration.visibility in [nil, :public]
    end)
  end

  defp remove_spans(source, spans) do
    spans
    |> Enum.map(&declaration_line_span(source, &1))
    |> Enum.sort_by(&elem(&1, 0))
    |> merge_ranges()
    |> Enum.sort_by(&elem(&1, 0), :desc)
    |> Enum.reduce(source, fn {start_byte, end_byte}, acc ->
      binary_part(acc, 0, start_byte) <> binary_part(acc, end_byte, byte_size(acc) - end_byte)
    end)
  end

  defp remove_import_spans([], source), do: source

  defp remove_import_spans(spans, source) do
    spans
    |> Enum.map(&import_line_span(source, &1))
    |> Enum.sort_by(&elem(&1, 0))
    |> merge_ranges()
    |> Enum.sort_by(&elem(&1, 0), :desc)
    |> Enum.reduce(source, fn {start_byte, end_byte}, acc ->
      binary_part(acc, 0, start_byte) <> binary_part(acc, end_byte, byte_size(acc) - end_byte)
    end)
  end

  defp merge_ranges([]), do: []

  defp merge_ranges([{start_byte, end_byte} | rest]) do
    Enum.reduce(rest, [{start_byte, end_byte}], fn {next_start, next_end}, [{current_start, current_end} | tail] ->
      if next_start <= current_end,
        do: [{current_start, max(current_end, next_end)} | tail],
        else: [{next_start, next_end}, {current_start, current_end} | tail]
    end)
    |> Enum.reverse()
  end

  defp declaration_line_span(source, %Span{start_byte: start_byte, end_byte: end_byte}) do
    {leading_start(source, line_start(source, start_byte)), line_end(source, end_byte)}
  end

  defp import_line_span(source, %Span{start_byte: start_byte, end_byte: end_byte}) do
    {line_start(source, start_byte), line_end(source, end_byte)}
  end

  # A declaration's documentation comments and decorators are trivia attached
  # to the AST node, not necessarily part of its token span. Carry adjacent
  # comment/attribute lines with the declaration so extraction remains lossless
  # and source removal does not strand them above the next declaration.
  defp leading_start(source, start_byte) do
    previous = previous_line_start(source, start_byte)

    if previous < start_byte and movable_trivia_line?(source, previous) do
      leading_start(source, previous)
    else
      start_byte
    end
  end

  defp previous_line_start(_source, 0), do: 0

  defp previous_line_start(source, start_byte) do
    before = binary_part(source, 0, max(start_byte - 1, 0))

    case :binary.matches(before, "\n") |> List.last() do
      {index, 1} -> index + 1
      nil -> 0
    end
  end

  defp movable_trivia_line?(source, start_byte) do
    end_byte = line_end(source, start_byte)
    line = source |> binary_part(start_byte, end_byte - start_byte) |> String.trim()
    String.starts_with?(line, "#") or String.starts_with?(line, "@")
  end

  defp line_start(_source, 0), do: 0

  defp line_start(source, offset) do
    source
    |> binary_part(0, offset)
    |> :binary.matches("\n")
    |> List.last()
    |> case do
      {index, 1} -> index + 1
      nil -> 0
    end
  end

  defp line_end(source, offset) do
    suffix = binary_part(source, offset, byte_size(source) - offset)

    case :binary.match(suffix, "\n") do
      {index, 1} -> offset + index + 1
      :nomatch -> byte_size(source)
    end
  end

  defp insert_imports(source, _report, []), do: source

  defp insert_imports(source, report, imports) do
    offset = module_header_end(source, report.path)

    text = Enum.map_join(imports, "", &"  #{&1}\n")
    binary_part(source, 0, offset) <> text <> binary_part(source, offset, byte_size(source) - offset)
  end

  defp module_header_end(source, path) do
    case parse_source(source, path) do
      {:ok, ast} ->
        case module_span(ast) do
          %Span{start_byte: start_byte} -> line_end(source, start_byte)
          _ -> byte_size(source)
        end

      _ ->
        byte_size(source)
    end
  end

  defp span_from_map(%{
         start_byte: start_byte,
         end_byte: end_byte,
         start_line: start_line,
         start_column: start_column,
         end_line: end_line,
         end_column: end_column,
         source_id: source_id,
         path: path
       }),
       do: %Span{
         source_id: source_id,
         path: path,
         start_byte: start_byte,
         end_byte: end_byte,
         start_line: start_line,
         start_column: start_column,
         end_line: end_line,
         end_column: end_column
       }

  defp span_from_map(_), do: nil

  defp build_target(source, report, selected, extra_imports, target_module, source_path) do
    prefix = module_prefix(source, source_path)
    imports = Enum.map(report.imports, &import_source(source, &1)) ++ extra_imports
    declarations = Enum.map(selected, fn declaration -> declaration_source(source, declaration) end)
    body = (imports ++ declarations) |> Enum.reject(&(&1 == "")) |> Enum.map(&indent_block/1) |> Enum.join("\n\n")
    [prefix, "mod #{target_module}\n", if(body == "", do: "", else: body <> "\n"), "end\n"] |> IO.iodata_to_binary()
  end

  defp module_prefix(source, path) do
    case parse_source(source, path) do
      {:ok, ast} ->
        case module_span(ast) do
          %Span{start_byte: start_byte} ->
            prefix = binary_part(source, 0, start_byte)
            String.trim_trailing(prefix, "\n") <> if(prefix == "", do: "", else: "\n")

          _ ->
            ""
        end

      _ ->
        ""
    end
  end

  defp module_span({:container, meta, _body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module, do: source_span(meta), else: nil
  end

  defp module_span({:block, _meta, items}) when is_list(items),
    do: Enum.find_value(items, &module_span/1)

  defp module_span(_), do: nil

  defp source_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Span{} = span} -> span
      _ -> nil
    end
  end

  defp import_source(source, import) do
    case span_from_map(import.span) do
      %Span{start_byte: start_byte, end_byte: end_byte} ->
        binary_part(source, start_byte, end_byte - start_byte) |> String.trim()

      _ ->
        ""
    end
  end

  defp declaration_source(source, %Declaration{span: %Span{} = span}) do
    {start_byte, end_byte} = declaration_line_span(source, span)
    binary_part(source, start_byte, end_byte - start_byte) |> String.trim()
  end

  defp declaration_source(_source, _declaration), do: ""

  defp indent_block(text) do
    text
    |> dedent()
    |> String.split("\n", trim: false)
    |> Enum.map_join("\n", &"  #{&1}")
  end

  defp dedent(text) do
    lines = String.split(text, "\n", trim: false)

    widths =
      lines
      |> Enum.reject(&(String.trim(&1) == ""))
      |> Enum.map(fn line -> line |> String.replace(~r/[^ ].*$/, "") |> byte_size() end)

    width = if widths == [], do: 0, else: Enum.min(widths)

    Enum.map_join(lines, "\n", fn line ->
      if byte_size(line) >= width, do: binary_part(line, width, byte_size(line) - width), else: line
    end)
  end

  defp verify_generated(module, source, path) do
    case parse_source(source, path) do
      {:ok, ast} ->
        if module_name(ast) == module, do: :ok, else: {:error, {:generated_module_error, path, module}}

      {:error, errors} ->
        {:error, {:generated_parse_error, path, errors}}
    end
  end

  defp parse_source(source, path) do
    with {:ok, tokens, trivia} <- Lexer.tokenize(source, file: path, emit_events: false, trivia: true),
         {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false) do
      {:ok, Trivia.attach(ast, trivia)}
    else
      {:error, errors} when is_list(errors) -> {:error, errors}
      {:error, reason} -> {:error, [reason]}
    end
  end

  defp module_name({:container, meta, _body}) when is_list(meta), do: meta |> Keyword.get(:name) |> to_string()
  defp module_name({:block, _meta, items}), do: items |> Enum.find_value(&module_name/1)
  defp module_name(_), do: nil

  defp maybe_write(generated, opts) do
    if Keyword.get(opts, :write, false) do
      with :ok <- File.mkdir_p(Path.dirname(generated.target_path)),
           :ok <- write_file(generated.target_path, generated.target),
           :ok <- write_file(generated.source_path, generated.source) do
        {:ok, true}
      end
    else
      {:ok, false}
    end
  end

  defp maybe_write_source(path, contents, opts) do
    if Keyword.get(opts, :write, false), do: write_file(path, contents), else: :ok
  end

  defp write_file(path, contents) do
    case File.write(path, contents) do
      :ok -> :ok
      {:error, reason} -> {:error, {:write_error, path, reason}}
    end
  end
end
