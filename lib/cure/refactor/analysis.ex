defmodule Cure.Refactor.Analysis.Declaration do
  @moduledoc "A source-level declaration record used by the refactor analyzer."

  @enforce_keys [:name, :kind, :identity, :arity, :visibility, :span, :line_count, :source_order]
  defstruct [
    :name,
    :kind,
    :identity,
    :arity,
    :visibility,
    :span,
    :line_count,
    :source_order
  ]

  @type t :: %__MODULE__{
          name: String.t(),
          kind: atom(),
          identity: atom() | nil,
          arity: non_neg_integer() | nil,
          visibility: atom() | nil,
          span: Cure.Diagnostic.Span.t() | nil,
          line_count: pos_integer(),
          source_order: pos_integer()
        }
end

defmodule Cure.Refactor.Analysis.Report do
  @moduledoc "Deterministic read-only analysis of one Cure source module."

  @enforce_keys [:path, :module, :source_hash, :line_count, :declaration_count, :imports, :declarations]
  defstruct [
    :path,
    :module,
    :source_hash,
    :line_count,
    :declaration_count,
    :imports,
    :declarations,
    warnings: [],
    checked?: false
  ]

  @type t :: %__MODULE__{
          path: Path.t(),
          module: String.t(),
          source_hash: String.t(),
          line_count: pos_integer(),
          declaration_count: non_neg_integer(),
          imports: [map()],
          declarations: [Cure.Refactor.Analysis.Declaration.t()],
          warnings: [map()],
          checked?: boolean()
        }
end

defmodule Cure.Refactor.Analysis do
  @moduledoc """
  Canonical, read-only source analysis for `mix cure.refactor`.

  The analyzer deliberately stops at the parsed module boundary. It reports
  authored declarations and imports in source order, preserving canonical
  declaration identities and exact source spans. It never edits a source file
  and never infers a split from line ranges. A future planning/apply phase can
  build on this record after a declaration-level dependency projection is
  exposed by the checked compiler pipeline.

  Prelude macro expansion is opt-in (`prelude_macros: true`). Keeping the
  default syntax-only makes analysis cheap and deterministic for large files;
  callers that need expansion-aware syntax can request it explicitly.
  """

  alias Cure.Compiler.{Lexer, Parser, Trivia}
  alias Cure.Diagnostic.Span
  alias Cure.Elab.{Name, Program}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  alias Cure.Refactor.Analysis.{Declaration, Report}

  @type error ::
          {:file_read_error, Path.t(), atom()}
          | {:usage_error, String.t()}
          | {:parse_error, [term()]}
          | {:trivia_error, term()}
          | {:module_not_found, Path.t()}
          | term()

  @doc "Analyze one `.cure` source file without modifying it."
  @spec analyze(Path.t(), keyword()) :: {:ok, Report.t()} | {:error, error()}
  def analyze(path, opts \\ []) when is_binary(path) do
    expanded = Path.expand(path)

    with :ok <- validate_source_path(expanded),
         {:ok, source} <- read_source(expanded),
         {:ok, ast} <- parse_source(source, expanded, opts),
         {:ok, module, body, extras} <- module_body(ast, expanded),
         {:ok, checked?} <- maybe_check(expanded, opts) do
      declarations = declarations(body, module, source)
      imports = imports(body)
      warnings = out_of_module_warnings(extras)

      {:ok,
       %Report{
         path: expanded,
         module: module,
         source_hash: source_hash(source),
         line_count: line_count(source),
         declaration_count: length(declarations),
         imports: imports,
         declarations: declarations,
         warnings: warnings,
         checked?: checked?
       }}
    end
  end

  @doc "Encode a report as deterministic JSON suitable for tooling."
  @spec to_json(Report.t()) :: String.t()
  def to_json(%Report{} = report), do: report |> to_map() |> Jason.encode!()

  @doc "Return the JSON-compatible map representation of a report."
  @spec to_map(Report.t()) :: map()
  def to_map(%Report{} = report) do
    %{
      path: report.path,
      module: report.module,
      source_hash: report.source_hash,
      line_count: report.line_count,
      declaration_count: report.declaration_count,
      checked: report.checked?,
      imports: Enum.map(report.imports, &import_to_map/1),
      declarations: Enum.map(report.declarations, &declaration_to_map/1),
      warnings: report.warnings
    }
  end

  @doc "Render the compact human-readable report used by the Mix task."
  @spec format(Report.t()) :: String.t()
  def format(%Report{} = report) do
    declaration_lines =
      Enum.map(report.declarations, fn declaration ->
        span = format_span(declaration.span)
        visibility = declaration.visibility || :n_a
        arity = if is_integer(declaration.arity), do: "/#{declaration.arity}", else: ""

        "  #{declaration.source_order}. #{declaration.identity || declaration.name}#{arity} " <>
          "(#{declaration.kind}, #{visibility}, #{span})"
      end)

    ([
       "Module: #{report.module}",
       "Path: #{report.path}",
       "Source hash: #{report.source_hash}",
       "Lines: #{report.line_count}",
       "Declarations: #{report.declaration_count}",
       "Imports: #{length(report.imports)}",
       "Checked: #{report.checked?}",
       "",
       "Declarations:"
     ] ++ declaration_lines ++ [""])
    |> Enum.join("\n")
  end

  defp validate_source_path(path) do
    if Path.extname(path) == ".cure" do
      :ok
    else
      {:error, {:usage_error, "refactor analysis requires a `.cure` source: #{path}"}}
    end
  end

  defp read_source(path) do
    case File.read(path) do
      {:ok, source} -> {:ok, source}
      {:error, reason} -> {:error, {:file_read_error, path, reason}}
    end
  end

  defp parse_source(source, path, opts) do
    lexer_opts = [file: path, emit_events: false, trivia: true]

    with {:ok, tokens, trivia} <- Lexer.tokenize(source, lexer_opts),
         {:ok, ast} <-
           Parser.parse(tokens,
             file: path,
             emit_events: false,
             prelude_macros: Keyword.get(opts, :prelude_macros, false)
           ) do
      try do
        {:ok, Trivia.attach(ast, trivia)}
      rescue
        error in Cure.Compiler.Trivia.UnplacedTriviaError ->
          {:error, {:trivia_error, error.item}}
      end
    else
      {:error, errors} when is_list(errors) -> {:error, {:parse_error, errors}}
      {:error, reason} -> {:error, {:parse_error, [reason]}}
    end
  end

  defp maybe_check(path, opts) do
    if Keyword.get(opts, :checked, false) do
      check_opts = [
        module_pipeline: :canonical,
        package: Keyword.get(opts, :package, "refactor"),
        source_roots: Keyword.get(opts, :source_roots, [Path.dirname(path)]),
        interface_roots: Keyword.get(opts, :interface_roots, []),
        products: [],
        publication: nil,
        fresh_environment: true
      ]

      case Cure.Compiler.ModulePipeline.check([path], check_opts) do
        {:ok, _result} -> {:ok, true}
        {:error, reason} -> {:error, reason}
      end
    else
      {:ok, false}
    end
  end

  defp module_body(ast, path) do
    case locate_module(ast) do
      {:ok, meta, body, extras} ->
        case Keyword.get(meta, :name) do
          name when is_binary(name) and name != "" -> {:ok, name, List.wrap(body), extras}
          name when is_atom(name) -> {:ok, Atom.to_string(name), List.wrap(body), extras}
          _ -> {:error, {:module_not_found, path}}
        end

      :error ->
        {:error, {:module_not_found, path}}
    end
  end

  defp locate_module({:container, meta, body}) when is_list(meta) do
    if Keyword.get(meta, :container_type) == :module, do: {:ok, meta, body, []}, else: :error
  end

  defp locate_module({:block, _meta, items}) when is_list(items) do
    case Enum.with_index(items) |> Enum.find(fn {node, _index} -> module_container?(node) end) do
      {{:container, meta, body}, index} ->
        extras =
          items
          |> Enum.with_index()
          |> Enum.reject(fn {_node, candidate_index} -> candidate_index == index end)
          |> Enum.map(&elem(&1, 0))
          |> Enum.filter(&Program.declaration?/1)

        {:ok, meta, body, extras}

      nil ->
        :error
    end
  end

  defp locate_module(_other), do: :error

  defp module_container?({:container, meta, _body}) when is_list(meta),
    do: Keyword.get(meta, :container_type) == :module

  defp module_container?(_other), do: false

  defp out_of_module_warnings([]), do: []

  defp out_of_module_warnings(extras) do
    first = List.first(extras)
    {tag, meta, _body} = first

    [
      %{
        kind: "declarations_outside_module",
        count: length(extras),
        first_kind: Atom.to_string(tag),
        first_name: declaration_name(meta, tag),
        first_span: span_to_map(node_span(meta))
      }
    ]
  end

  defp imports(body) do
    body
    |> Enum.with_index(1)
    |> Enum.flat_map(fn
      {{:import, meta, items}, source_order} when is_list(meta) ->
        source = Keyword.get(meta, :source)

        if is_binary(source) or is_atom(source) do
          [
            %{
              source: to_string(source),
              import_type: Keyword.get(meta, :import_type, :use) |> to_string(),
              public: Keyword.get(meta, :public, false) == true,
              items: normalize_items(items),
              source_order: source_order,
              span: span_to_map(node_span(meta))
            }
          ]
        else
          []
        end

      _ ->
        []
    end)
  end

  defp declarations(body, module, source) do
    body
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {node, source_order} ->
      if Program.declaration?(node) do
        [declaration(node, module, source, source_order)]
      else
        []
      end
    end)
  end

  defp declaration({:function_def, meta, _body}, module, source, source_order) do
    named_declaration(meta, module, source, source_order, :function)
  end

  defp declaration({:macro_def, meta, _rules}, module, source, source_order) do
    named_declaration(meta, module, source, source_order, :macro)
  end

  defp declaration({:type_annotation, meta, _rhs}, module, source, source_order) do
    named_declaration(meta, module, source, source_order, :typealias)
  end

  defp declaration({:indexed_type, meta, _body}, module, source, source_order) do
    named_declaration(meta, module, source, source_order, :indexed_type)
  end

  defp declaration({tag, meta, _body}, module, source, source_order)
       when tag in [:interface, :implementation] do
    named_declaration(meta, module, source, source_order, tag)
  end

  defp declaration({:container, meta, _body}, module, source, source_order) do
    kind = Keyword.get(meta, :container_type, :container)
    named_declaration(meta, module, source, source_order, kind)
  end

  defp named_declaration(meta, module, source, source_order, kind) do
    name = declaration_name(meta, kind)
    identity = if is_binary(name) and name != "", do: Name.qualify(module, name), else: nil
    span = node_span(meta)
    arity = if kind in [:function, :macro], do: declaration_arity(meta), else: nil
    visibility = if kind in [:function, :macro], do: Keyword.get(meta, :visibility, :public), else: nil

    %Declaration{
      name: name || Atom.to_string(kind),
      kind: kind,
      identity: identity,
      arity: arity,
      visibility: visibility,
      span: span,
      line_count: span_line_count(span, source),
      source_order: source_order
    }
  end

  defp declaration_name(meta, _kind) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> name
      name when is_atom(name) -> Atom.to_string(name)
      _ -> nil
    end
  end

  defp declaration_arity(meta) do
    case Keyword.get(meta, :arity) do
      arity when is_integer(arity) and arity >= 0 -> arity
      _ -> meta |> Keyword.get(:params, []) |> List.wrap() |> length()
    end
  end

  defp node_span(meta) when is_list(meta) do
    case Metadata.source_info(meta) do
      %SourceInfo{whole: %Span{} = span} -> span
      _ -> nil
    end
  end

  defp span_line_count(%Span{start_line: first, end_line: last}, _source), do: max(last - first + 1, 1)
  defp span_line_count(_span, _source), do: 1

  defp line_count(source), do: source |> String.split("\n", trim: false) |> length()

  defp source_hash(source) do
    :sha256
    |> :crypto.hash(source)
    |> Base.encode16(case: :lower)
  end

  defp normalize_items(items) when is_list(items), do: Enum.map(items, &normalize_item/1)
  defp normalize_items(_items), do: []

  defp normalize_item(item) when is_binary(item) or is_atom(item), do: to_string(item)
  defp normalize_item(item), do: inspect(item, limit: :infinity, printable_limit: 256)

  defp declaration_to_map(%Declaration{} = declaration) do
    %{
      name: declaration.name,
      kind: Atom.to_string(declaration.kind),
      identity: if(declaration.identity, do: Atom.to_string(declaration.identity)),
      arity: declaration.arity,
      visibility: if(declaration.visibility, do: Atom.to_string(declaration.visibility)),
      line_count: declaration.line_count,
      source_order: declaration.source_order,
      span: span_to_map(declaration.span)
    }
  end

  defp import_to_map(import), do: Map.update!(import, :span, & &1)

  defp span_to_map(nil), do: nil

  defp span_to_map(%Span{} = span) do
    %{
      source_id: span.source_id,
      path: span.path,
      start_byte: span.start_byte,
      end_byte: span.end_byte,
      start_line: span.start_line,
      start_column: span.start_column,
      end_line: span.end_line,
      end_column: span.end_column
    }
  end

  defp format_span(nil), do: "unknown span"

  defp format_span(%Span{start_line: line, start_column: column, end_line: end_line, end_column: end_column}),
    do: "#{line}:#{column}-#{end_line}:#{end_column}"
end
