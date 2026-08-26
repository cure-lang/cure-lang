defmodule Cure.Compiler.ModulePipeline.Cycle do
  @moduledoc """
  Classifies a strongly connected component of the module graph.

  Two modules that call each other at runtime are ordinary: their signatures are
  explicit, so each can be checked against the other's frozen interface and
  neither needs the other to reduce. A cycle only becomes fatal when an edge
  needs a peer's *body* for definitional equality — `A.T = B.F(A.T)` where `B.F`
  computes over `A.T` — because then neither module can be checked first and no
  ordering exists.

  The distinction is decided here, before registration, so the failure is
  reported as the cycle it is. Left to the elaborator it surfaces as whichever
  name happened to be looked up first (`{:unknown_global, :F}`), which names a
  symptom in one module and says nothing about the loop.
  """

  alias Cure.Compiler.ModuleManifest
  alias Cure.Compiler.ModuleSkeleton

  @type identity :: {String.t(), String.t()}

  @doc """
  `:ok` unless this component contains a type-level reference to a peer's value
  definition, in which case the component is a compile-time cycle.
  """
  @spec classify(ModuleManifest.t(), [identity()], %{identity() => term()}, %{identity() => ModuleSkeleton.t()}) ::
          :ok | {:error, term()}
  def classify(_manifest, component, _asts, _skeletons) when length(component) < 2, do: :ok

  def classify(%ModuleManifest{} = manifest, component, asts, skeletons) do
    members = MapSet.new(component)

    Enum.find_value(component, :ok, fn identity ->
      with {:ok, ast} <- Map.fetch(asts, identity),
           {:ok, {peer, declaration}} <- body_requiring_reference(ast, identity, members, skeletons) do
        {:error,
         {:compile_time_cycle,
          %{
            path: cycle_path(manifest, component, identity, peer),
            requires_body: %{declaration: declaration.key, span: declaration.span}
          }}}
      else
        _ -> nil
      end
    end)
  end

  # A qualified name used inside a TYPE declaration that resolves to a peer's
  # value declaration. The namespace is what makes it compile-time: naming a
  # peer's type in a type is an ordinary interface edge, but naming a peer's
  # function there means that function has to run before this module has a type.
  defp body_requiring_reference(ast, identity, members, skeletons) do
    ast
    |> type_declarations()
    |> Enum.flat_map(&qualified_names/1)
    |> Enum.find_value(:error, fn {owner, base} ->
      peer = {elem(identity, 0), owner}

      with true <- peer != identity,
           true <- MapSet.member?(members, peer),
           %ModuleSkeleton{} = skeleton <- Map.get(skeletons, peer),
           %ModuleSkeleton.Declaration{} = declaration <- Map.get(skeleton.declarations, {:value, base}) do
        {:ok, {peer, declaration}}
      else
        _ -> nil
      end
    end)
  end

  defp type_declarations(node) when is_tuple(node) do
    own =
      case node do
        {:type_annotation, meta, _} when is_list(meta) -> [node]
        {:container, meta, _} when is_list(meta) -> if type_container?(meta), do: [node], else: []
        _ -> []
      end

    own ++ (node |> Tuple.to_list() |> type_declarations())
  end

  defp type_declarations(nodes) when is_list(nodes), do: Enum.flat_map(nodes, &type_declarations/1)
  defp type_declarations(_leaf), do: []

  defp type_container?(meta),
    do: Keyword.get(meta, :container_type) in [:enum, :struct, :opaque, :primitive]

  # `Owner.Path.base` reaches a type declaration either as a call's dotted name
  # (`Cycle.MetaB.F(T)`) or as a bare dotted variable. Both spell the same edge.
  defp qualified_names(node) when is_tuple(node) do
    own =
      case node do
        {tag, meta, _} when tag in [:function_call, :variable] and is_list(meta) ->
          split_owner(Keyword.get(meta, :name))

        _ ->
          []
      end

    own ++ (node |> Tuple.to_list() |> qualified_names())
  end

  defp qualified_names(nodes) when is_list(nodes), do: Enum.flat_map(nodes, &qualified_names/1)
  defp qualified_names(name) when is_binary(name), do: split_owner(name)
  defp qualified_names(_leaf), do: []

  defp split_owner(name) when is_binary(name) do
    case String.split(name, ".") do
      [_bare] -> []
      parts -> [{parts |> Enum.drop(-1) |> Enum.join("."), List.last(parts)}]
    end
  end

  defp split_owner(_name), do: []

  # The loop as the author can walk it: from the module whose type needs a body,
  # through the peer that owns it, back along checked edges to the start.
  defp cycle_path(manifest, component, from, to) do
    names = [elem(from, 1) | Enum.map(return_path(manifest, component, to, from), &elem(&1, 1))]
    names ++ [elem(from, 1)]
  end

  defp return_path(manifest, component, from, target) do
    members = MapSet.new(component)
    search(manifest, members, [[from]], MapSet.new([from]), target)
  end

  defp search(_manifest, _members, [], _seen, _target), do: []

  defp search(manifest, members, [[head | _] = path | queue], seen, target) do
    neighbours =
      manifest.dependencies
      |> Map.get(head, [])
      |> Enum.map(& &1.target)
      |> Enum.filter(&MapSet.member?(members, &1))
      |> Enum.uniq()

    cond do
      target in neighbours ->
        Enum.reverse(path)

      true ->
        fresh = Enum.reject(neighbours, &MapSet.member?(seen, &1))
        seen = Enum.reduce(fresh, seen, &MapSet.put(&2, &1))
        search(manifest, members, queue ++ Enum.map(fresh, &[&1 | path]), seen, target)
    end
  end
end
