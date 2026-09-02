defmodule Cure.Refactor.Analysis.Reference do
  @moduledoc "A source-level reference recorded for dependency-aware analysis."

  @enforce_keys [:name, :identity, :kind, :span]
  defstruct [:name, :identity, :kind, :span]

  @type t :: %__MODULE__{
          name: String.t(),
          identity: atom() | nil,
          kind: atom(),
          span: Cure.Diagnostic.Span.t() | nil
        }
end

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
    :source_order,
    depth: 0,
    parent: nil,
    children: [],
    references: []
  ]

  @type t :: %__MODULE__{
          name: String.t(),
          kind: atom(),
          identity: atom() | nil,
          arity: non_neg_integer() | nil,
          visibility: atom() | nil,
          span: Cure.Diagnostic.Span.t() | nil,
          line_count: pos_integer(),
          source_order: pos_integer(),
          depth: non_neg_integer(),
          parent: atom() | nil,
          children: [t()],
          references: [Cure.Refactor.Analysis.Reference.t()]
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
    stats: %{},
    plan: nil,
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
          stats: map(),
          plan: map() | nil,
          warnings: [map()],
          checked?: boolean()
        }
end

defmodule Cure.Refactor.Analysis do
  @moduledoc """
  Canonical, read-only source analysis for `mix cure.refactor`.

  The analyzer deliberately stops at the parsed module boundary. It reports
  authored declarations and imports in source order, preserving canonical
  declaration identities and exact source spans. Recursive mode adds a nested
  declaration tree without treating ordinary expressions as members; stats are
  deterministic and derived from that tree. Dependency mode records a
  syntax-level call projection, canonicalizing names proven local and leaving
  imported or otherwise unresolved names explicit. It never edits a source
  file and never infers a split from line ranges. Plan mode derives a
  dependency-only component graph and labels components with no local edges as
  isolated candidates; it does not apply a split or claim that moving a
  declaration preserves module identity.

  Prelude macro expansion is opt-in (`prelude_macros: true`). Keeping the
  default syntax-only makes analysis cheap and deterministic for large files;
  callers that need expansion-aware syntax can request it explicitly.
  """

  alias Cure.Compiler.{Lexer, Parser, Trivia}
  alias Cure.Diagnostic.Span
  alias Cure.Elab.{Name, Program}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  alias Cure.Refactor.Analysis.{Declaration, Reference, Report}

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
         {:ok, opts} <- validate_analysis_options(opts),
         {:ok, source} <- read_source(expanded),
         {:ok, ast} <- parse_source(source, expanded, opts),
         {:ok, module, body, extras} <- module_body(ast, expanded),
         {:ok, checked?} <- maybe_check(expanded, opts) do
      dependencies? = Keyword.get(opts, :dependencies, false) or Keyword.get(opts, :plan, false)
      declarations = declarations(body, module, source, Keyword.put(opts, :dependencies, dependencies?))
      imports = imports(body)
      warnings = out_of_module_warnings(extras)

      stats =
        if Keyword.get(opts, :stats, false),
          do: statistics(declarations, imports),
          else: %{}

      plan = if Keyword.get(opts, :plan, false), do: dependency_plan(declarations), else: nil

      {:ok,
       %Report{
         path: expanded,
         module: module,
         source_hash: source_hash(source),
         line_count: line_count(source),
         declaration_count: length(declarations),
         imports: imports,
         declarations: declarations,
         stats: stats,
         plan: plan,
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
      stats: report.stats,
      plan: plan_to_map(report.plan),
      warnings: report.warnings
    }
  end

  @doc "Render the compact human-readable report used by the Mix task."
  @spec format(Report.t(), keyword()) :: String.t()
  def format(%Report{} = report, opts \\ []) do
    declaration_lines =
      Enum.flat_map(
        report.declarations,
        &format_declaration(
          &1,
          Keyword.get(opts, :recursive, false),
          Keyword.get(opts, :dependencies, false)
        )
      )

    import_lines =
      if Keyword.get(opts, :verbose, false) do
        ["", "Imports:"] ++ Enum.map(report.imports, &format_import/1)
      else
        []
      end

    stats_lines =
      if report.stats == %{} do
        []
      else
        ["", "Stats:"] ++ format_statistics(report.stats)
      end

    plan_lines =
      if report.plan == nil do
        []
      else
        ["", "Dependency plan:"] ++ format_plan(report.plan)
      end

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
     ] ++ declaration_lines ++ import_lines ++ stats_lines ++ plan_lines ++ [""])
    |> Enum.join("\n")
  end

  defp validate_source_path(path) do
    if Path.extname(path) == ".cure" do
      :ok
    else
      {:error, {:usage_error, "refactor analysis requires a `.cure` source: #{path}"}}
    end
  end

  defp validate_analysis_options(opts) do
    case Keyword.get(opts, :max_depth, :infinity) do
      :infinity -> {:ok, opts}
      depth when is_integer(depth) and depth >= 0 -> {:ok, opts}
      depth -> {:error, {:usage_error, "--max-depth must be a non-negative integer, got: #{inspect(depth)}"}}
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

  defp declarations(body, module, source, opts) do
    recursive? = Keyword.get(opts, :recursive, false)
    max_depth = Keyword.get(opts, :max_depth, :infinity)
    dependencies? = Keyword.get(opts, :dependencies, false)
    local_names = local_declaration_names(body)

    {declarations, _next_order} =
      Enum.reduce(body, {[], 1}, fn node, {acc, next_order} ->
        if Program.declaration?(node) do
          {declaration, next_order} =
            declaration_tree(
              node,
              module,
              source,
              next_order,
              0,
              nil,
              recursive?,
              max_depth,
              dependencies?,
              local_names
            )

          {[declaration | acc], next_order}
        else
          {acc, next_order}
        end
      end)

    Enum.reverse(declarations)
  end

  defp local_declaration_names(body) do
    body
    |> Enum.filter(&Program.declaration?/1)
    |> Enum.map(fn {_tag, meta, _body} -> declaration_name(meta, nil) end)
    |> Enum.filter(&(is_binary(&1) and &1 != ""))
    |> MapSet.new()
  end

  defp declaration_tree(
         node,
         module,
         source,
         source_order,
         depth,
         parent,
         recursive?,
         max_depth,
         dependencies?,
         local_names
       ) do
    declaration = declaration(node, module, source, source_order)
    declaration = %{declaration | depth: depth, parent: parent}

    declaration =
      if dependencies? do
        %{declaration | references: references(node, module, local_names)}
      else
        declaration
      end

    if recursive? and below_depth_limit?(depth, max_depth) do
      {children, next_order} =
        node
        |> nested_declaration_nodes()
        |> Enum.reduce({[], source_order + 1}, fn child, {acc, next_order} ->
          {nested, next_order} =
            declaration_tree(
              child,
              module,
              source,
              next_order,
              depth + 1,
              declaration.identity,
              recursive?,
              max_depth,
              dependencies?,
              local_names
            )

          {[nested | acc], next_order}
        end)

      {%{declaration | children: Enum.reverse(children)}, next_order}
    else
      {declaration, source_order + 1}
    end
  end

  defp below_depth_limit?(_depth, :infinity), do: true
  defp below_depth_limit?(depth, max_depth), do: depth < max_depth

  # Declarations are represented by arbitrary AST nodes. Walk their third
  # field and stop at the next declaration so each child owns traversal of its
  # own body. This finds interface members and nested `where` declarations
  # without mistaking ordinary function calls for structural members.
  defp nested_declaration_nodes(node) when is_tuple(node) and tuple_size(node) == 3,
    do: node |> elem(2) |> collect_declaration_nodes()

  defp collect_declaration_nodes(items) when is_list(items),
    do: Enum.flat_map(items, &collect_declaration_nodes/1)

  defp collect_declaration_nodes({tag, meta, children} = node) when is_atom(tag) and is_list(meta) do
    if Program.declaration?(node), do: [node], else: collect_declaration_nodes(children)
  end

  defp collect_declaration_nodes(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.flat_map(&collect_declaration_nodes/1)

  defp collect_declaration_nodes(map) when is_map(map),
    do: map |> Map.values() |> Enum.flat_map(&collect_declaration_nodes/1)

  defp collect_declaration_nodes(_other), do: []

  defp format_declaration(declaration, recursive?, dependencies?) do
    indent = String.duplicate("  ", declaration.depth)
    span = format_span(declaration.span)
    visibility = declaration.visibility || :n_a
    arity = if is_integer(declaration.arity), do: "/#{declaration.arity}", else: ""

    line =
      "#{indent}#{declaration.source_order}. #{declaration.identity || declaration.name}#{arity} " <>
        "(#{declaration.kind}, #{visibility}, #{span})"

    references =
      if dependencies? and declaration.references != [] do
        [
          "#{indent}  references: " <>
            Enum.map_join(declaration.references, ", ", &format_reference/1)
        ]
      else
        []
      end

    children =
      if recursive? do
        Enum.flat_map(
          declaration.children,
          &format_declaration(&1, true, dependencies?)
        )
      else
        []
      end

    [line | references ++ children]
  end

  defp format_reference(%Reference{name: name, identity: identity, kind: kind}) do
    target = if identity, do: Atom.to_string(identity), else: name
    "#{target} (#{kind})"
  end

  defp format_import(import) do
    items = if import.items == [], do: "", else: " (#{Enum.join(import.items, ", ")})"
    "  #{import.source_order}. #{import.import_type} #{import.source}#{items}"
  end

  defp statistics(declarations, imports) do
    all = flatten_declarations(declarations)
    references = Enum.flat_map(all, & &1.references)

    %{
      "top_level_declarations" => length(declarations),
      "total_declarations" => length(all),
      "nested_declarations" => max(length(all) - length(declarations), 0),
      "max_depth" => if(all == [], do: 0, else: Enum.max_by(all, & &1.depth).depth),
      "declarations_by_kind" => frequencies(all, &Atom.to_string(&1.kind)),
      "declarations_by_visibility" => frequencies(all, &to_string(&1.visibility || :n_a)),
      "imports_by_source" => frequencies(imports, & &1.source),
      "references" => length(references),
      "unresolved_references" => Enum.count(references, &is_nil(&1.identity)),
      "references_by_kind" => frequencies(references, &Atom.to_string(&1.kind))
    }
  end

  defp flatten_declarations(declarations),
    do: Enum.flat_map(declarations, fn declaration -> [declaration | flatten_declarations(declaration.children)] end)

  defp frequencies(items, selector), do: items |> Enum.map(selector) |> Enum.frequencies() |> sort_map()

  defp sort_map(map), do: map |> Enum.sort_by(&elem(&1, 0)) |> Map.new()

  defp format_statistics(stats) do
    [
      "  top-level declarations: #{stats["top_level_declarations"]}",
      "  total declarations: #{stats["total_declarations"]}",
      "  nested declarations: #{stats["nested_declarations"]}",
      "  maximum depth: #{stats["max_depth"]}",
      "  declarations by kind: #{inspect(stats["declarations_by_kind"], pretty: false)}",
      "  declarations by visibility: #{inspect(stats["declarations_by_visibility"], pretty: false)}",
      "  imports by source: #{inspect(stats["imports_by_source"], pretty: false)}",
      "  references: #{stats["references"]} (#{stats["unresolved_references"]} unresolved)",
      "  references by kind: #{inspect(stats["references_by_kind"], pretty: false)}"
    ]
  end

  # The planner intentionally works on top-level declarations only. Nested
  # declarations (interface members and `where` helpers) are owned by their
  # enclosing declaration and cannot be moved without a separate surface
  # rewrite. Strongly connected components are the smallest units that must
  # move together to preserve local dependency edges.
  defp dependency_plan(declarations) do
    top_level = Enum.filter(declarations, &(&1.depth == 0 and is_atom(&1.identity)))

    groups =
      top_level
      |> Enum.group_by(& &1.identity)
      |> Enum.map(fn {identity, members} ->
        %{identity: identity, members: Enum.sort_by(members, & &1.source_order)}
      end)
      |> Enum.sort_by(fn group -> List.first(group.members).source_order end)

    group_index =
      groups
      |> Enum.with_index()
      |> Map.new(fn {group, index} -> {group.identity, index} end)

    edges =
      groups
      |> Enum.with_index()
      |> Map.new(fn {group, index} ->
        targets =
          group.members
          |> Enum.flat_map(& &1.references)
          |> Enum.map(& &1.identity)
          |> Enum.map(&Map.get(group_index, &1))
          |> Enum.reject(&is_nil/1)
          |> Enum.uniq()
          |> Enum.sort()

        {index, targets}
      end)

    components = strongly_connected_components(edges, length(groups))
    component_for = component_membership(components)
    component_records = build_component_records(groups, edges, components, component_for)
    cross_component_edges = count_cross_component_edges(edges, component_for)
    isolated = Enum.count(component_records, & &1.isolated?)
    cyclic = Enum.count(component_records, & &1.cyclic?)
    boundary_references = Enum.reduce(component_records, 0, &(&1.boundary_reference_count + &2))
    unresolved_references = Enum.reduce(component_records, 0, &(&1.unresolved_reference_count + &2))

    %{
      components: component_records,
      component_count: length(component_records),
      isolated_candidates: isolated,
      cyclic_components: cyclic,
      cross_component_edges: cross_component_edges,
      boundary_references: boundary_references,
      unresolved_references: unresolved_references
    }
  end

  defp strongly_connected_components(_edges, 0), do: []

  defp strongly_connected_components(edges, count) do
    state = %{next_index: 0, stack: [], on_stack: MapSet.new(), indices: %{}, lowlinks: %{}, components: []}

    state =
      Enum.reduce(0..(count - 1), state, fn node, state ->
        if Map.has_key?(state.indices, node), do: state, else: tarjan_visit(node, state, edges)
      end)

    state.components
    |> Enum.map(&Enum.sort/1)
    |> Enum.sort_by(&List.first/1)
  end

  defp tarjan_visit(node, state, edges) do
    index = state.next_index

    state = %{
      state
      | next_index: index + 1,
        indices: Map.put(state.indices, node, index),
        lowlinks: Map.put(state.lowlinks, node, index),
        stack: [node | state.stack],
        on_stack: MapSet.put(state.on_stack, node)
    }

    state =
      edges
      |> Map.get(node, [])
      |> Enum.reduce(state, fn target, state ->
        cond do
          not Map.has_key?(state.indices, target) ->
            state = tarjan_visit(target, state, edges)
            lowlink = min(state.lowlinks[node], state.lowlinks[target])
            %{state | lowlinks: Map.put(state.lowlinks, node, lowlink)}

          MapSet.member?(state.on_stack, target) ->
            lowlink = min(state.lowlinks[node], state.indices[target])
            %{state | lowlinks: Map.put(state.lowlinks, node, lowlink)}

          true ->
            state
        end
      end)

    if state.lowlinks[node] == state.indices[node] do
      {component, stack, on_stack} = pop_component(node, state.stack, state.on_stack, [])
      %{state | stack: stack, on_stack: on_stack, components: [component | state.components]}
    else
      state
    end
  end

  defp pop_component(node, [node | rest], on_stack, component),
    do: {[node | component], rest, MapSet.delete(on_stack, node)}

  defp pop_component(node, [head | rest], on_stack, component),
    do: pop_component(node, rest, MapSet.delete(on_stack, head), [head | component])

  defp component_membership(components) do
    components
    |> Enum.with_index()
    |> Enum.flat_map(fn {members, component} -> Enum.map(members, &{&1, component}) end)
    |> Map.new()
  end

  defp build_component_records(groups, edges, components, component_for) do
    components
    |> Enum.with_index()
    |> Enum.map(fn {members, component_index} ->
      groups_in_component = Enum.map(members, &Enum.at(groups, &1))
      declarations = Enum.flat_map(groups_in_component, & &1.members) |> Enum.sort_by(& &1.source_order)
      outgoing = component_edges(members, edges, component_for, component_index)
      incoming = incoming_component_edges(component_index, edges, component_for)
      source_orders = Enum.map(declarations, & &1.source_order)
      spans = declarations |> Enum.map(& &1.span) |> Enum.reject(&is_nil/1)
      line_start = spans |> Enum.map(& &1.start_line) |> Enum.min(fn -> nil end)
      line_end = spans |> Enum.map(& &1.end_line) |> Enum.max(fn -> nil end)
      self_edge? = Enum.any?(members, fn member -> member in Map.get(edges, member, []) end)
      cyclic? = length(members) > 1 or self_edge?
      isolated? = outgoing == [] and incoming == []
      representative = declarations |> List.first() |> Map.get(:identity)
      references = Enum.flat_map(declarations, & &1.references)
      local_identities = MapSet.new(Enum.map(declarations, & &1.identity))
      boundary_references = Enum.reject(references, &MapSet.member?(local_identities, &1.identity))
      unresolved_references = Enum.count(boundary_references, &is_nil(&1.identity))

      %{
        id: "component_#{component_index + 1}",
        representative: representative,
        declarations: Enum.map(declarations, & &1.identity),
        source_orders: source_orders,
        line_start: line_start,
        line_end: line_end,
        line_count: if(line_start && line_end, do: line_end - line_start + 1, else: 0),
        dependencies: Enum.map(outgoing, &"component_#{&1 + 1}"),
        dependents: Enum.map(incoming, &"component_#{&1 + 1}"),
        cyclic?: cyclic?,
        isolated?: isolated?,
        public?: Enum.any?(declarations, &(&1.visibility == :public)),
        boundary_reference_count: length(boundary_references),
        unresolved_reference_count: unresolved_references,
        boundary_references: boundary_references |> Enum.map(& &1.name) |> Enum.uniq() |> Enum.sort()
      }
    end)
  end

  defp component_edges(members, edges, component_for, component_index) do
    members
    |> Enum.flat_map(&Map.get(edges, &1, []))
    |> Enum.map(&Map.get(component_for, &1))
    |> Enum.reject(&(&1 == component_index or is_nil(&1)))
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp incoming_component_edges(component_index, edges, component_for) do
    edges
    |> Enum.flat_map(fn {source, targets} ->
      if Enum.any?(targets, &(Map.get(component_for, &1) == component_index)),
        do: [Map.get(component_for, source)],
        else: []
    end)
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp count_cross_component_edges(edges, component_for) do
    Enum.reduce(edges, 0, fn {source, targets}, count ->
      source_component = Map.get(component_for, source)

      count +
        Enum.count(targets, fn target ->
          source_component != Map.get(component_for, target)
        end)
    end)
  end

  defp format_plan(plan) do
    summary = [
      "  components: #{plan.component_count}",
      "  isolated candidates: #{plan.isolated_candidates}",
      "  cyclic components: #{plan.cyclic_components}",
      "  cross-component edges: #{plan.cross_component_edges}",
      "  boundary references: #{plan.boundary_references} (#{plan.unresolved_references} unresolved)"
    ]

    components =
      Enum.flat_map(plan.components, fn component ->
        flags =
          cond do
            component.isolated? -> "isolated candidate"
            component.cyclic? -> "cyclic"
            true -> "dependency component"
          end

        boundary =
          if component.boundary_references == [],
            do: "none",
            else: Enum.join(component.boundary_references, ",")

        [
          "  #{component.id}: #{flags}; " <>
            "declarations=#{Enum.map_join(component.declarations, ", ", &Atom.to_string/1)}; " <>
            "depends_on=#{format_component_ids(component.dependencies)}; " <>
            "dependents=#{format_component_ids(component.dependents)}; " <>
            "boundary=#{boundary}"
        ]
      end)

    summary ++ components
  end

  defp format_component_ids([]), do: "none"
  defp format_component_ids(ids), do: Enum.join(ids, ",")

  defp references(node, module, local_names) do
    node
    |> collect_references([])
    |> Enum.reverse()
    |> Enum.uniq_by(&{&1.name, &1.kind, &1.span})
    |> Enum.map(fn %{name: name, kind: kind, span: span} ->
      %Reference{
        name: name,
        identity: reference_identity(name, module, local_names),
        kind: kind,
        span: span
      }
    end)
  end

  defp collect_references({:function_call, meta, args}, acc) when is_list(meta) do
    acc =
      case Keyword.get(meta, :name) do
        name when is_binary(name) or is_atom(name) ->
          [%{name: to_string(name), kind: reference_kind(meta), span: node_span(meta)} | acc]

        _ ->
          acc
      end

    acc = collect_references(args, acc)
    collect_references(Keyword.values(meta), acc)
  end

  defp collect_references({tag, meta, children}, acc) when is_atom(tag) and is_list(meta) do
    acc = collect_references(children, acc)
    collect_references(Keyword.values(meta), acc)
  end

  defp collect_references(items, acc) when is_list(items),
    do: Enum.reduce(items, acc, &collect_references/2)

  defp collect_references(tuple, acc) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.reduce(acc, &collect_references/2)

  defp collect_references(map, acc) when is_map(map),
    do: map |> Map.values() |> Enum.reduce(acc, &collect_references/2)

  defp collect_references(_other, acc), do: acc

  defp reference_kind(meta) do
    cond do
      Keyword.get(meta, :function_type, false) -> :type
      Keyword.get(meta, :record, false) -> :record
      true -> :call
    end
  end

  defp reference_identity(name, module, local_names) do
    cond do
      MapSet.member?(local_names, name) -> Name.qualify(module, name)
      String.contains?(name, ".") -> qualified_identity(name)
      true -> nil
    end
  end

  defp qualified_identity(name) do
    case String.split(name, ".", trim: true) do
      parts when length(parts) >= 2 ->
        member = List.last(parts)
        owner = parts |> Enum.drop(-1) |> Enum.join(".")
        Name.qualify(owner, member)

      _ ->
        nil
    end
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
      depth: declaration.depth,
      parent: if(declaration.parent, do: Atom.to_string(declaration.parent)),
      line_count: declaration.line_count,
      source_order: declaration.source_order,
      span: span_to_map(declaration.span),
      children: Enum.map(declaration.children, &declaration_to_map/1),
      references: Enum.map(declaration.references, &reference_to_map/1)
    }
  end

  defp plan_to_map(nil), do: nil

  defp plan_to_map(plan) do
    plan
    |> Map.update!(:components, fn components ->
      Enum.map(components, fn component ->
        component
        |> Map.update!(:representative, &identity_to_string/1)
        |> Map.update!(:declarations, fn identities -> Enum.map(identities, &identity_to_string/1) end)
      end)
    end)
  end

  defp identity_to_string(nil), do: nil
  defp identity_to_string(identity) when is_atom(identity), do: Atom.to_string(identity)
  defp identity_to_string(identity), do: to_string(identity)

  defp reference_to_map(%Reference{} = reference) do
    %{
      name: reference.name,
      identity: if(reference.identity, do: Atom.to_string(reference.identity)),
      kind: Atom.to_string(reference.kind),
      span: span_to_map(reference.span)
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
