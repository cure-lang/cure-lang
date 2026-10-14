defmodule Cure.LSP.Docs do
  @moduledoc """
  Documentation hover for the language server.

  Resolves the name under the cursor to its declaration and renders the
  declaration's signature followed by its `##` documentation, the way ElixirLS
  shows `@doc` and `@moduledoc`. A name resolves, in order:

    1. qualified (`Std.List.map`, `L.map` under `use Std.List as L`) -- in the
       named module, which may be the open document itself;
    2. unqualified -- in the module around the cursor (`:line` in the
       context) and the modules enclosing it, then in every module the
       document `use`s;
    3. a capitalised name that is neither -- as a module (`use Std.List`).

  Modules are read from the open documents first, so unsaved edits show up,
  then from disk through `Cure.REPL.Docs.locate_source/2` (the bundled stdlib
  plus the directories in the context's `:roots`). Parsed files are cached in
  the process dictionary by path and file stat.
  """

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.MetaAST.Metadata

  @cache_key {__MODULE__, :declarations}

  @typedoc """
  Where to look for modules the document refers to: the open documents by URI,
  and extra source directories. `:line` is the cursor's 1-based line.
  """
  @type context :: %{
          optional(:documents) => %{String.t() => String.t()},
          optional(:roots) => [String.t()],
          optional(:line) => pos_integer()
        }

  @doc """
  Markdown hover for the dotted `name` ending at the cursor, or `nil` when it
  names no declaration.
  """
  @spec hover(term(), String.t(), context()) :: String.t() | nil
  def hover(ast, name, context \\ %{}) do
    case String.split(name, ".", trim: true) do
      [] -> nil
      segments -> segments |> resolve(ast, context) |> render()
    end
  end

  # -- Resolution ---------------------------------------------------------------

  defp resolve([first | _] = segments, ast, context) do
    {qualifier, [name]} = Enum.split(segments, -1)

    cond do
      qualifier == [] -> resolve_unqualified(name, ast, context)
      lowercase?(first) -> resolve_unqualified(name, ast, context)
      true -> resolve_qualified(Enum.join(qualifier, "."), name, ast, context)
    end
  end

  defp resolve_unqualified(name, ast, context) do
    imported = fn -> Enum.find_value(imports(ast), &find(module_declarations(&1.source, ast, context), name)) end
    local = ast |> declarations() |> in_scope(enclosing_module(ast, Map.get(context, :line)))

    find(local, name) || imported.() ||
      if(lowercase?(name), do: nil, else: find_module(module_declarations(name, ast, context), name))
  end

  defp resolve_qualified(qualifier, name, ast, context) do
    module = expand_alias(qualifier, imports(ast))
    full = module <> "." <> name

    find(module_declarations(module, ast, context), name) ||
      if(lowercase?(name), do: nil, else: find_module(module_declarations(full, ast, context), full))
  end

  # The declarations visible unqualified from inside `scope`: its own, those
  # of the modules enclosing it, and the top-level ones. Without a cursor
  # line every declaration in the document is.
  defp in_scope(declarations, nil), do: declarations

  defp in_scope(declarations, scope) do
    Enum.filter(declarations, &(&1.module == nil or &1.module == scope or String.starts_with?(scope, &1.module <> ".")))
  end

  # The innermost module whose source span holds `line`, named the way
  # `declarations/1` names it.
  defp enclosing_module(_ast, nil), do: nil
  defp enclosing_module(ast, line), do: enclosing_module(ast, line, nil)

  defp enclosing_module({:block, _, children}, line, module) when is_list(children),
    do: Enum.find_value(children, &enclosing_module(&1, line, module))

  defp enclosing_module({:container, meta, body}, line, module) when is_list(meta) and is_list(body) do
    if Keyword.get(meta, :container_type) not in [:enum, :struct] and spans_line?(meta, line) do
      nested = qualify(module, to_string(Keyword.get(meta, :name, "unknown")))
      Enum.find_value(body, &enclosing_module(&1, line, nested)) || nested
    end
  end

  defp enclosing_module(_node, _line, _module), do: nil

  defp spans_line?(meta, line) do
    case Metadata.source_info(meta) do
      %{whole: %{start_line: first, end_line: last}} -> line in first..last//1
      _ -> false
    end
  end

  defp find(declarations, name) do
    case Enum.filter(declarations, &(&1.name == name)) do
      [] -> nil
      [%{kind: :function} | _] = matches -> {:functions, Enum.filter(matches, &(&1.kind == :function))}
      [first | _] -> first
    end
  end

  defp find_module(declarations, name) do
    Enum.find(declarations, &(&1.kind == :module and same_module?(&1.name, name)))
  end

  # `Std.` is optional when naming a stdlib module, as in `Cure.REPL.Docs`.
  defp same_module?(declared, requested) do
    declared == requested or declared == "Std." <> requested or "Std." <> declared == requested
  end

  defp expand_alias(qualifier, imports) do
    case Enum.find(imports, &(&1.alias == qualifier)) do
      %{source: source} -> source
      nil -> qualifier
    end
  end

  defp imports(ast) do
    ast
    |> collect(fn
      {:import, meta, _} when is_list(meta) ->
        case Keyword.get(meta, :source) do
          source when is_binary(source) -> [%{source: source, alias: alias_name(Keyword.get(meta, :alias))}]
          _ -> []
        end

      _ ->
        []
    end)
  end

  defp alias_name(name) when is_binary(name), do: name
  defp alias_name(name) when is_atom(name) and not is_nil(name), do: Atom.to_string(name)
  defp alias_name(_), do: nil

  # The declarations of `module`: from the open document when it declares the
  # module, else from another open document, else from disk.
  defp module_declarations(module, ast, context) do
    local = declarations(ast)

    if declares?(local, module) do
      in_module(local, module)
    else
      open_module_declarations(module, context) || disk_module_declarations(module, context)
    end
  end

  # A document may declare several modules; only `module`'s own declarations
  # (and the top-level ones, which include the module itself) belong to it.
  defp in_module(declarations, module) do
    Enum.filter(declarations, &(&1.module == nil or same_module?(&1.module, module)))
  end

  defp declares?(declarations, module) do
    Enum.any?(declarations, &(&1.kind == :module and same_module?(&1.name, module)))
  end

  defp open_module_declarations(module, context) do
    context
    |> Map.get(:documents, %{})
    |> Map.values()
    |> Enum.find_value(fn text ->
      with true <- declares_module?(text, module),
           {:ok, ast} <- parse(text),
           found = declarations(ast),
           true <- declares?(found, module) do
        in_module(found, module)
      else
        _ -> nil
      end
    end)
  end

  defp disk_module_declarations(module, context) do
    case Cure.REPL.Docs.locate_source(module, %{roots: Map.get(context, :roots, [])}) do
      {:ok, path} -> cached_file_declarations(path)
      :not_found -> []
    end
  end

  # A cheap scan before parsing; `mod` lines may be nested, so a module's last
  # segment is enough to make the document worth parsing.
  defp declares_module?(text, module) do
    last = module |> String.split(".") |> List.last()

    ~r/^\s*mod\s+([A-Za-z_][\w.]*)/m
    |> Regex.scan(text, capture: :all_but_first)
    |> Enum.any?(fn [declared] -> same_module?(declared, module) or String.ends_with?(declared, last) end)
  end

  defp cached_file_declarations(path) do
    cache = Process.get(@cache_key, %{})
    stat = File.stat(path)

    case Map.get(cache, path) do
      {^stat, declarations} ->
        declarations

      _ ->
        declarations =
          with {:ok, text} <- File.read(path),
               {:ok, ast} <- parse(text, path) do
            declarations(ast)
          else
            _ -> []
          end

        Process.put(@cache_key, Map.put(cache, path, {stat, declarations}))
        declarations
    end
  end

  defp parse(text, file \\ "nofile") do
    with {:ok, tokens} <- Lexer.tokenize(text, file: file, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: file, emit_events: false) do
      {:ok, ast}
    end
  rescue
    _ -> :error
  end

  # -- Declarations ---------------------------------------------------------------

  @doc """
  Every documentable declaration in `ast`, each tagged with its enclosing
  module (`nil` at the top level).
  """
  @spec declarations(term()) :: [map()]
  def declarations(ast), do: declarations(ast, nil)

  defp declarations({:block, _, children}, module) when is_list(children),
    do: Enum.flat_map(children, &declarations(&1, module))

  defp declarations({:container, meta, body}, module) when is_list(meta) and is_list(body) do
    name = to_string(Keyword.get(meta, :name, "unknown"))
    doc = doc(meta)

    case Keyword.get(meta, :container_type) do
      :enum ->
        type = %{kind: :type, name: name, module: module, doc: doc, header: enum_header(name, meta, body)}
        constructors = for {:function_def, cmeta, _} <- body, do: constructor(cmeta, name, module)
        [type | constructors]

      :struct ->
        [%{kind: :type, name: name, module: module, doc: doc, header: record_header(name, body)}]

      container_type ->
        nested = qualify(module, name)
        keyword = container_keyword(container_type)
        header = "#{keyword} #{nested}"

        [
          %{kind: :module, name: nested, module: module, doc: doc, header: header}
          | Enum.flat_map(body, &declarations(&1, nested))
        ]
    end
  end

  defp declarations({:interface, meta, body}, module) when is_list(meta) do
    name = to_string(Keyword.get(meta, :name, "unknown"))
    params = Keyword.get(meta, :params, [])

    header =
      if params == [], do: "interface #{name}", else: "interface #{name}(#{Enum.map_join(params, ", ", &to_string/1)})"

    methods = if is_list(body), do: Enum.flat_map(body, &declarations(&1, module)), else: []
    [%{kind: :interface, name: name, module: module, doc: doc(meta), header: header} | methods]
  end

  defp declarations({:type_annotation, meta, children}, module) when is_list(meta) do
    name = to_string(Keyword.get(meta, :name, "unknown"))

    header =
      case children do
        [definition | _] -> "type #{name} = #{render_type(definition)}"
        _ -> "type #{name}"
      end

    [%{kind: :type, name: name, module: module, doc: doc(meta), header: header}]
  end

  defp declarations({:function_def, meta, _body}, module) when is_list(meta) do
    if Keyword.has_key?(meta, :variant) do
      []
    else
      name = to_string(Keyword.get(meta, :name, "unknown"))
      [%{kind: :function, name: name, module: module, doc: doc(meta), header: function_header(name, meta)}]
    end
  end

  defp declarations(_node, _module), do: []

  defp constructor(meta, type, module) do
    name = to_string(Keyword.get(meta, :name, "unknown"))

    %{
      kind: :constructor,
      name: name,
      module: module,
      type: type,
      doc: doc(meta),
      header: constructor_header(name, meta)
    }
  end

  defp container_keyword(:module), do: "mod"
  defp container_keyword(:proof), do: "proof"
  defp container_keyword(:protocol), do: "interface"
  defp container_keyword(other) when is_atom(other) and not is_nil(other), do: Atom.to_string(other)
  defp container_keyword(_), do: "mod"

  # A module nested in another is spelled with its full path.
  defp qualify(nil, name), do: name

  defp qualify(module, name) do
    if String.starts_with?(name, module <> "."), do: name, else: module <> "." <> name
  end

  defp doc(meta) do
    case Keyword.get(meta, :doc) do
      doc when is_binary(doc) -> if String.trim(doc) == "", do: nil, else: String.trim(doc)
      _ -> nil
    end
  end

  # -- Signatures -----------------------------------------------------------------

  defp function_header(name, meta) do
    params = meta |> Keyword.get(:params, []) |> List.wrap() |> Enum.map_join(", ", &render_param/1)
    head = "#{name}(#{params})"

    head =
      case Keyword.get(meta, :return_type) do
        nil -> head
        type -> head <> " -> " <> render_type(type)
      end

    case Keyword.get(meta, :effects) do
      effects when is_list(effects) and effects != [] -> head <> " ! " <> Enum.map_join(effects, ", ", &render_effect/1)
      _ -> head
    end
  end

  defp constructor_header(name, meta) do
    case Keyword.get(meta, :params, []) do
      params when is_list(params) and params != [] -> "#{name}(#{Enum.map_join(params, ", ", &render_param/1)})"
      _ -> name
    end
  end

  defp enum_header(name, meta, body) do
    params = Keyword.get(meta, :type_params, [])
    head = if params == [], do: name, else: "#{name}(#{Enum.map_join(params, ", ", &render_type/1)})"

    variants =
      for {:function_def, cmeta, _} <- body, do: constructor_header(to_string(Keyword.get(cmeta, :name)), cmeta)

    if variants == [], do: "type #{head}", else: "type #{head} = #{Enum.join(variants, " | ")}"
  end

  defp record_header(name, fields) do
    lines = for {:param, meta, field} <- fields, do: "  #{field}: #{render_type(Keyword.get(meta, :type))}"
    Enum.join(["rec #{name}" | lines], "\n")
  end

  defp render_param({:param, meta, name}) when is_list(meta) do
    binder = if label = Keyword.get(meta, :label), do: "#{label} #{name}", else: to_string(name)

    case Keyword.get(meta, :type) do
      nil -> binder
      type -> binder <> ": " <> render_type(type)
    end
  end

  defp render_param(other), do: render_type(other)

  defp render_type(nil), do: "Any"
  defp render_type(name) when is_binary(name), do: name
  defp render_type(name) when is_atom(name), do: Atom.to_string(name)

  defp render_type({:variable, _, name}) when is_binary(name) or is_atom(name), do: to_string(name)

  # The parser spells an arrow type `a -> b` as `Function(a, b)`.
  defp render_type({:function_call, meta, args}) when is_list(meta) and is_list(args) do
    name = to_string(Keyword.get(meta, :name, "?"))

    cond do
      Keyword.get(meta, :function_type) && args != [] ->
        {domain, [codomain]} = Enum.split(args, -1)
        render_domain(domain) <> " -> " <> render_type(codomain)

      args == [] ->
        name

      true ->
        "#{name}(#{Enum.map_join(args, ", ", &render_type/1)})"
    end
  end

  defp render_type(ast) do
    Printer.quoted_to_string(ast)
  rescue
    _ -> "?"
  end

  defp render_domain([{:function_call, meta, _} = single]) when is_list(meta) do
    if Keyword.get(meta, :function_type), do: "(#{render_type(single)})", else: render_type(single)
  end

  defp render_domain([single]), do: render_type(single)
  defp render_domain(domain), do: "(#{Enum.map_join(domain, ", ", &render_type/1)})"

  defp render_effect(effect) when is_atom(effect), do: effect |> Atom.to_string() |> Macro.camelize()
  defp render_effect(effect), do: render_type(effect)

  # -- Rendering --------------------------------------------------------------------

  defp render(nil), do: nil

  defp render({:functions, functions}) do
    signatures = functions |> Enum.map(&qualified_header/1) |> Enum.uniq() |> Enum.join("\n")
    docs = functions |> Enum.map(& &1.doc) |> Enum.reject(&is_nil/1) |> Enum.uniq()
    markdown(signatures, docs)
  end

  defp render(%{kind: :constructor, type: type} = constructor) do
    note = "*Constructor of type `#{qualify(constructor.module, type)}`.*"
    markdown(constructor.header, [note | List.wrap(constructor.doc)])
  end

  defp render(declaration), do: markdown(declaration.header, List.wrap(declaration.doc))

  defp qualified_header(%{module: nil, header: header}), do: header
  defp qualified_header(%{module: module, header: header}), do: module <> "." <> header

  defp markdown(signature, []), do: "```cure\n#{signature}\n```"
  defp markdown(signature, docs), do: "```cure\n#{signature}\n```\n\n---\n\n" <> Enum.join(docs, "\n\n")

  # -- Helpers --------------------------------------------------------------------

  defp collect({_, _, children} = node, fun) when is_list(children) do
    fun.(node) ++ Enum.flat_map(children, &collect(&1, fun))
  end

  defp collect(node, fun) when is_tuple(node), do: fun.(node)
  defp collect(_node, _fun), do: []

  defp lowercase?(name), do: name =~ ~r/^[a-z_]/
end
