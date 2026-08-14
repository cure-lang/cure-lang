defmodule Cure.Elab.TotalityGraph do
  @moduledoc """
  Untrusted definition-graph analysis for totality certification.

  This occupies the role of Agda's `TermCheck.termMutual`: it turns a scheduling
  region into its actual recursive SCCs. Unlike Agda, it also emits a finite
  partition witness which `Cure.Core.Kernel` can check without trusting this
  module or rerunning SCC discovery.
  """

  alias Cure.Core.Env

  @partition_version 1

  @doc "Propose a deterministic SCC partition and its checkable witnesses."
  @spec propose_partition(Env.t(), [atom()]) :: map()
  def propose_partition(%Env{} = env, names) when is_list(names) do
    started = System.monotonic_time(:microsecond)
    universe = names |> Enum.map(&Env.resolve_key(env, env.defs, &1)) |> Enum.uniq() |> Enum.sort()
    universe_set = MapSet.new(universe)
    edges = direct_edges(env, universe, universe_set)

    components = strongly_connected_components(universe, edges)

    component_of =
      Enum.flat_map(components, fn members ->
        id = hd(members)
        Enum.map(members, &{&1, id})
      end)
      |> Map.new()

    ranks = component_ranks(components, component_of, edges)

    component_records =
      Map.new(components, fn members ->
        id = hd(members)
        root = hd(members)

        {id,
         %{
           members: members,
           root: root,
           forward_tree: spanning_tree(root, members, edges, :forward),
           reverse_tree: spanning_tree(root, members, edges, :reverse)
         }}
      end)

    sealed_boundaries =
      universe
      |> Enum.flat_map(fn source -> Env.direct_call_summary(env, source).calls end)
      |> Enum.map(& &1.callee)
      |> Enum.reject(&MapSet.member?(universe_set, &1))
      |> Enum.uniq()
      |> Enum.filter(fn callee ->
        Env.total?(env, callee) and is_binary(Map.get(env.totality_component_of, callee))
      end)
      |> Map.new(&{&1, Map.fetch!(env.totality_component_of, &1)})

    certificate = %{
      version: @partition_version,
      universe: universe,
      summary_hashes:
        Map.new(universe, fn name ->
          {name, env |> Env.direct_call_summary(name) |> Map.fetch!(:summary_hash)}
        end),
      component_of: component_of,
      rank: ranks,
      components: component_records,
      edges: edges,
      sealed_boundaries: sealed_boundaries
    }

    Cure.Pipeline.Events.emit(
      :type_checker,
      :totality_metric,
      %{
        operation: :scc_proposal,
        definitions: length(universe),
        components: map_size(component_records),
        direct_edges: length(edges),
        elapsed_us: System.monotonic_time(:microsecond) - started
      },
      %{}
    )

    certificate
  end

  defp direct_edges(env, universe, universe_set) do
    universe
    |> Enum.flat_map(fn source ->
      env
      |> Env.direct_call_summary(source)
      |> Map.fetch!(:calls)
      |> Enum.with_index()
      |> Enum.flat_map(fn {call, ordinal} ->
        if MapSet.member?(universe_set, call.callee) do
          [%{id: {source, call.id, ordinal}, source: source, target: call.callee}]
        else
          []
        end
      end)
    end)
    |> Enum.sort_by(fn edge -> {edge.source, edge.target, edge.id} end)
  end

  # Agda delegates this search to its recursivity checker. Cure deliberately
  # keeps it here, outside the TCB; the returned trees/ranks are the trusted
  # verifier's evidence.
  defp strongly_connected_components(vertices, edges) do
    graph = :digraph.new()

    try do
      Enum.each(vertices, &:digraph.add_vertex(graph, &1))
      Enum.each(edges, &:digraph.add_edge(graph, &1.id, &1.source, &1.target, :direct_call))

      graph
      |> :digraph_utils.strong_components()
      |> Enum.map(&Enum.sort/1)
      |> Enum.sort()
    after
      :digraph.delete(graph)
    end
  end

  # With call edges oriented caller -> callee, downstream components receive a
  # lower rank. Thus every inter-component edge is strictly rank-decreasing.
  defp component_ranks(components, component_of, edges) do
    ids = Enum.map(components, &hd/1)

    outgoing =
      Enum.reduce(edges, %{}, fn edge, acc ->
        source = Map.fetch!(component_of, edge.source)
        target = Map.fetch!(component_of, edge.target)

        if source == target,
          do: acc,
          else: Map.update(acc, source, MapSet.new([target]), &MapSet.put(&1, target))
      end)

    partial = Enum.reduce(ids, %{}, fn id, memo -> elem(rank_component(id, outgoing, memo), 1) end)

    # The verifier uses a strict total topological rank. Sorting first by the
    # longest-path rank preserves every caller>callee constraint; sorting by id
    # gives unrelated components deterministic, distinct ranks.
    partial
    |> Enum.sort_by(fn {id, rank} -> {rank, id} end)
    |> Enum.with_index()
    |> Map.new(fn {{id, _partial_rank}, rank} -> {id, rank} end)
  end

  defp rank_component(id, outgoing, memo) do
    case Map.fetch(memo, id) do
      {:ok, _rank} ->
        {Map.fetch!(memo, id), memo}

      :error ->
        {target_ranks, memo} =
          outgoing
          |> Map.get(id, MapSet.new())
          |> Enum.sort()
          |> Enum.map_reduce(memo, fn target, acc -> rank_component(target, outgoing, acc) end)

        rank =
          case target_ranks do
            [] -> 0
            ranks -> Enum.max(ranks) + 1
          end

        {rank, Map.put(memo, id, rank)}
    end
  end

  defp spanning_tree(_root, [_singleton], _edges, _direction), do: []

  defp spanning_tree(root, members, edges, direction) do
    member_set = MapSet.new(members)

    adjacency =
      edges
      |> Enum.filter(&(MapSet.member?(member_set, &1.source) and MapSet.member?(member_set, &1.target)))
      |> Enum.reduce(%{}, fn edge, acc ->
        {from, to} = if direction == :forward, do: {edge.source, edge.target}, else: {edge.target, edge.source}
        Map.update(acc, from, [{to, edge.id}], &[{to, edge.id} | &1])
      end)
      |> Map.new(fn {node, outgoing} -> {node, Enum.sort(outgoing)} end)

    grow_tree([root], MapSet.new([root]), [], adjacency)
  end

  defp grow_tree([], _seen, tree, _adjacency), do: Enum.reverse(tree)

  defp grow_tree([node | rest], seen, tree, adjacency) do
    {rest, seen, tree} =
      Enum.reduce(Map.get(adjacency, node, []), {rest, seen, tree}, fn {target, edge_id}, {queue, visited, acc} ->
        if MapSet.member?(visited, target) do
          {queue, visited, acc}
        else
          {queue ++ [target], MapSet.put(visited, target), [edge_id | acc]}
        end
      end)

    grow_tree(rest, seen, tree, adjacency)
  end
end
