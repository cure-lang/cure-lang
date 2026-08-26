defmodule Cure.Compiler.ModuleSkeleton.Declaration do
  @moduledoc false

  @enforce_keys [:key, :name, :namespace, :visibility, :owner]
  defstruct key: nil,
            name: nil,
            namespace: nil,
            visibility: nil,
            owner: nil,
            span: nil,
            extent: nil,
            header: nil
end

defmodule Cure.Compiler.ModuleSkeleton do
  @moduledoc """
  Early declaration index for one canonical module.

  The skeleton breaks source-order dependence: it names every declaration a
  consumer may resolve, in its namespace, without elaborating a body. It is not
  a checked type — `Cure.Compiler.ModulePipeline.Interface` owns that.
  """

  alias Cure.Compiler.ModuleSkeleton.Declaration

  @enforce_keys [:identity, :module_name, :source_path]
  defstruct identity: nil,
            module_name: nil,
            source_path: nil,
            declarations: %{},
            reexports: []

  @type t :: %__MODULE__{}

  @module_container_types [:module, :proof]
  @type_container_types [:enum, :struct, :opaque, :primitive, :protocol, :trait]

  @spec collect(tuple() | list(), {String.t(), String.t()}, Path.t()) :: t()
  def collect(ast, {package, module_name} = identity, source_path) do
    body = module_body(ast, module_name)

    declarations =
      body
      |> Enum.flat_map(&declarations(&1, package, module_name))
      |> Map.new(&{{&1.namespace, &1.name}, &1})

    %__MODULE__{
      identity: identity,
      module_name: module_name,
      source_path: source_path,
      declarations: declarations,
      reexports: reexports(body)
    }
  end

  @doc "Modules this module reexports with `public use`."
  @spec reexports(list()) :: [String.t()]
  def reexports(body) when is_list(body) do
    body
    |> Enum.flat_map(fn
      {:import, meta, _} when is_list(meta) ->
        if Keyword.get(meta, :public, false) do
          case Keyword.get(meta, :source) do
            source when is_binary(source) -> [source]
            _ -> []
          end
        else
          []
        end

      _ ->
        []
    end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  # The module container is not always the root node: an item-level decorator
  # such as `@prelude` wraps it in a block. Search for the container that
  # declares this module rather than assuming the root shape.
  defp module_body(ast, module_name) do
    case find_module_container(ast, module_name) do
      {:container, _meta, body} when is_list(body) -> body
      {:container, _meta, body} -> [body]
      nil -> []
    end
  end

  defp find_module_container({:container, meta, _} = node, module_name) when is_list(meta) do
    if Keyword.get(meta, :container_type) in @module_container_types and
         Keyword.get(meta, :name) == module_name do
      node
    else
      nil
    end
  end

  defp find_module_container(node, module_name) when is_tuple(node) do
    node |> Tuple.to_list() |> find_module_container(module_name)
  end

  defp find_module_container(nodes, module_name) when is_list(nodes) do
    Enum.find_value(nodes, &find_module_container(&1, module_name))
  end

  defp find_module_container(_leaf, _module_name), do: nil

  defp declarations({:function_def, meta, _body} = node, package, module_name) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) ->
        [declaration(node, meta, package, module_name, :value, name)]

      _ ->
        []
    end
  end

  defp declarations({:type_annotation, meta, _body} = node, package, module_name) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> [declaration(node, meta, package, module_name, :type, name)]
      _ -> []
    end
  end

  defp declarations({:container, meta, body} = node, package, module_name) when is_list(meta) do
    case {Keyword.get(meta, :container_type), Keyword.get(meta, :name)} do
      {type, name} when type in @type_container_types and is_binary(name) ->
        constructors =
          body
          |> List.wrap()
          |> Enum.flat_map(fn
            {:function_def, ctor_meta, _} = ctor when is_list(ctor_meta) ->
              case Keyword.get(ctor_meta, :name) do
                ctor_name when is_binary(ctor_name) ->
                  [declaration(ctor, ctor_meta, package, module_name, :constructor, ctor_name)]

                _ ->
                  []
              end

            _ ->
              []
          end)

        [declaration(node, meta, package, module_name, :type, name) | constructors]

      _ ->
        []
    end
  end

  defp declarations({:interface, meta, body} = node, package, module_name) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) ->
        methods =
          body
          |> List.wrap()
          |> Enum.flat_map(fn
            {:function_def, method_meta, _} = method when is_list(method_meta) ->
              case Keyword.get(method_meta, :name) do
                method_name when is_binary(method_name) ->
                  [declaration(method, method_meta, package, module_name, :value, method_name)]

                _ ->
                  []
              end

            _ ->
              []
          end)

        [declaration(node, meta, package, module_name, :interface, name) | methods]

      _ ->
        []
    end
  end

  defp declarations({:macro_def, meta, _rules} = node, package, module_name) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> [declaration(node, meta, package, module_name, :macro, name)]
      _ -> []
    end
  end

  defp declarations({:fixity, meta, _} = node, package, module_name) when is_list(meta) do
    case Keyword.get(meta, :operator) do
      operator when is_binary(operator) ->
        [declaration(node, meta, package, module_name, :operator, operator)]

      _ ->
        []
    end
  end

  defp declarations(_node, _package, _module_name), do: []

  defp declaration(node, meta, package, module_name, namespace, name) do
    visibility = if Keyword.get(meta, :visibility, :public) == :private, do: :private, else: :public

    %Declaration{
      key: {package, module_name, namespace, name},
      name: name,
      namespace: namespace,
      visibility: visibility,
      owner: {package, module_name},
      span: source_span(meta),
      extent: extent_span(meta),
      header: node
    }
  end

  defp source_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  # The full source range of the declaration, including its body. `span` points
  # at the name for "here is what you referred to"; `extent` answers the
  # different question "which declaration is this position inside".
  defp extent_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end
end
