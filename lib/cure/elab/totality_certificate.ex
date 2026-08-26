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
    started = System.monotonic_time(:microsecond)
    members = Enum.sort(Enum.uniq(members))
    member_set = MapSet.new(members)
    base_keys = base_keys(env, members, member_set)

    base_edges =
      Map.new(base_keys, fn key ->
        edge = edge_from_key(key, {:base, key})
        {edge.id, edge}
      end)

    {edges, composition_attempts, admitted_edges} =
      complete(Map.values(base_edges), base_edges, %{}, %{}, 0, 0)

    certificate = %{
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

    Cure.Pipeline.Events.emit(
      :type_checker,
      :totality_metric,
      %{
        operation: :closure_generation,
        members: members,
        direct_edges: length(base_keys),
        closure_edges: map_size(edges),
        composition_attempts: composition_attempts,
        admitted_edges: admitted_edges,
        elapsed_us: System.monotonic_time(:microsecond) - started
      },
      %{}
    )

    certificate
  end

  @doc "Generate one exact closure certificate for every proposed SCC."
  @spec propose_all(Env.t(), map()) :: %{atom() => map()}
  def propose_all(%Env{} = env, partition) do
    partition.components
    |> Enum.filter(fn {component_id, component} ->
      recursive_component?(partition, component_id, component.members)
    end)
    |> Map.new(fn {component_id, component} ->
      {component_id, propose(env, component.members)}
    end)
  end

  defp recursive_component?(_partition, _component_id, [_left, _right | _rest]), do: true

  defp recursive_component?(partition, component_id, [_singleton]) do
    Enum.any?(partition.edges, fn edge ->
      partition.component_of[edge.source] == component_id and
        partition.component_of[edge.target] == component_id
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

  defp complete([], edges, _by_source, _by_target, attempts, admitted),
    do: {edges, attempts, admitted}

  defp complete([edge | work], edges, by_source, by_target, attempts, admitted) do
    successors = Map.get(by_source, edge.target, MapSet.new())
    predecessors = Map.get(by_target, edge.source, MapSet.new())
    self = if edge.source == edge.target, do: [{edge, edge}], else: []

    pairs =
      self ++
        Enum.map(successors, &{edge, Map.fetch!(edges, &1)}) ++
        Enum.map(predecessors, &{Map.fetch!(edges, &1), edge})

    {work, edges, attempts, admitted} =
      Enum.reduce(pairs, {work, edges, attempts, admitted}, fn
        {left, right}, {pending, known, attempt_count, admitted_count} ->
          case SizeChange.compose_edges(left, right) do
            {:ok, composed} ->
              key = {composed.source, composed.target, composed.matrix}
              id = edge_id(key)

              if Map.has_key?(known, id) do
                {pending, known, attempt_count + 1, admitted_count}
              else
                derived = Map.merge(composed, %{id: id, derivation: {:compose, left.id, right.id}})
                {[derived | pending], Map.put(known, id, derived), attempt_count + 1, admitted_count + 1}
              end

            :incompatible ->
              {pending, known, attempt_count + 1, admitted_count}
          end
      end)

    by_source = Map.update(by_source, edge.source, MapSet.new([edge.id]), &MapSet.put(&1, edge.id))
    by_target = Map.update(by_target, edge.target, MapSet.new([edge.id]), &MapSet.put(&1, edge.id))
    complete(work, edges, by_source, by_target, attempts, admitted)
  end

  defp edge_from_key({source, target, matrix} = key, derivation) do
    %{id: edge_id(key), source: source, target: target, matrix: matrix, derivation: derivation}
  end

  defp edge_id(key), do: :crypto.hash(:sha256, :erlang.term_to_binary(key, [:deterministic]))
end
