defmodule Cure.Elab.TotalityCertificate do
  @moduledoc """
  Untrusted exact size-change closure generator.

  This is Cure's counterpart to Agda's `Termination.completionStep`: only
  endpoint-compatible edges are composed, and each newly admitted edge carries
  a derivation the kernel can replay. Exact key equality is the sole pruning
  rule; Agda-style `Favorites` are deliberately not used yet.
  """

  alias Cure.Core.{Env, SizeChange}

  @version 1

  @spec propose(Env.t(), [atom()]) :: map()
  def propose(%Env{} = env, members) do
    members = Enum.sort(Enum.uniq(members))
    member_set = MapSet.new(members)
    base_keys = base_keys(env, members, member_set)

    base_edges =
      Map.new(base_keys, fn key ->
        edge = edge_from_key(key, {:base, key})
        {edge.id, edge}
      end)

    edges = complete(Map.values(base_edges), base_edges, %{}, %{})

    %{
      version: @version,
      members: members,
      member_body_hashes:
        Map.new(members, fn member ->
          {member, env |> Env.direct_call_summary(member) |> Map.fetch!(:body_hash)}
        end),
      direct_summary_hashes:
        Map.new(members, fn member ->
          {member, env |> Env.direct_call_summary(member) |> Map.fetch!(:summary_hash)}
        end),
      base_keys: base_keys,
      edges: edges
    }
  end

  @doc "Generate one exact closure certificate for every proposed SCC."
  @spec propose_all(Env.t(), map()) :: %{atom() => map()}
  def propose_all(%Env{} = env, partition) do
    Map.new(partition.components, fn {component_id, component} ->
      {component_id, propose(env, component.members)}
    end)
  end

  defp base_keys(env, members, member_set) do
    members
    |> Enum.flat_map(fn source ->
      for call <- Env.direct_call_summary(env, source).calls,
          MapSet.member?(member_set, call.callee) do
        {source, call.callee, SizeChange.sparse(call.matrix)}
      end
    end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp complete([], edges, _by_source, _by_target), do: edges

  defp complete([edge | work], edges, by_source, by_target) do
    successors = Map.get(by_source, edge.target, MapSet.new())
    predecessors = Map.get(by_target, edge.source, MapSet.new())
    self = if edge.source == edge.target, do: [{edge, edge}], else: []

    pairs =
      self ++
        Enum.map(successors, &{edge, Map.fetch!(edges, &1)}) ++
        Enum.map(predecessors, &{Map.fetch!(edges, &1), edge})

    {work, edges} =
      Enum.reduce(pairs, {work, edges}, fn {left, right}, {pending, known} ->
        case SizeChange.compose_edges(left, right) do
          {:ok, composed} ->
            key = {composed.source, composed.target, composed.matrix}
            id = edge_id(key)

            if Map.has_key?(known, id) do
              {pending, known}
            else
              derived = Map.merge(composed, %{id: id, derivation: {:compose, left.id, right.id}})
              {[derived | pending], Map.put(known, id, derived)}
            end

          :incompatible ->
            {pending, known}
        end
      end)

    by_source = Map.update(by_source, edge.source, MapSet.new([edge.id]), &MapSet.put(&1, edge.id))
    by_target = Map.update(by_target, edge.target, MapSet.new([edge.id]), &MapSet.put(&1, edge.id))
    complete(work, edges, by_source, by_target)
  end

  defp edge_from_key({source, target, matrix} = key, derivation) do
    %{id: edge_id(key), source: source, target: target, matrix: matrix, derivation: derivation}
  end

  defp edge_id(key), do: :crypto.hash(:sha256, :erlang.term_to_binary(key, [:deterministic]))
end
