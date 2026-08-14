defmodule Cure.Core.TotalityCertificate do
  @moduledoc """
  Trusted verifier for an externally generated exact size-change closure.

  The verifier replays finite `Base`/`Compose` evidence and checks saturation;
  it does not search for new closure edges. This mirrors Agda's completed call
  graph criterion while preserving Cure's explicit kernel boundary.
  """

  alias Cure.Core.{Env, SizeChange}

  @version 1

  @spec verify(Env.t(), [atom()], map()) ::
          {:ok, :total | {:not_total, map()}} | {:error, term()}
  def verify(%Env{} = env, members, %{version: @version} = candidate) do
    started = System.monotonic_time(:microsecond)
    members = Enum.sort(Enum.uniq(members))

    result =
      with :ok <- verify_identity(env, members, candidate),
           {:ok, expected_base_keys} <- expected_base_keys(env, members),
           :ok <- verify_base_keys(candidate, expected_base_keys),
           :ok <- verify_base_derivations(candidate, expected_base_keys),
           :ok <- verify_derivations(candidate, expected_base_keys),
           :ok <- verify_saturation(candidate) do
        bad =
          candidate.edges
          |> Map.values()
          |> Enum.sort_by(&{&1.source, &1.target, &1.matrix})
          |> Enum.find(fn edge ->
            edge.source == edge.target and SizeChange.idempotent?(edge.matrix) and
              not SizeChange.smaller_diagonal?(edge.matrix)
          end)

        if bad,
          do: {:ok, {:not_total, explain_bad_edge(bad, candidate.edges)}},
          else: {:ok, :total}
      end

    emit_metric(members, candidate, result, started)
    result
  end

  def verify(_env, _members, candidate),
    do: invalid(:unsupported_version, version: Map.get(candidate, :version))

  defp emit_metric(members, candidate, result, started) do
    outcome =
      case result do
        {:ok, :total} -> :total
        {:ok, {:not_total, _}} -> :not_total
        {:error, _} -> :invalid
      end

    Cure.Pipeline.Events.emit(
      :kernel,
      :totality_metric,
      %{
        operation: :closure_verification,
        members: members,
        direct_edges: length(Map.get(candidate, :base_keys, [])),
        closure_edges: map_size(Map.get(candidate, :edges, %{})),
        result: outcome,
        elapsed_us: System.monotonic_time(:microsecond) - started
      },
      %{}
    )
  end

  defp explain_bad_edge(edge, edges) do
    edge
    |> Map.put(:diagonal, SizeChange.diagonal(edge.matrix))
    |> Map.put(:source_call_path, derivation_base_path(edge, edges))
  end

  defp derivation_base_path(%{derivation: {:base, {source, target, _matrix}}}, _edges),
    do: [{source, target}]

  defp derivation_base_path(%{derivation: {:compose, left, right}}, edges) do
    derivation_base_path(Map.fetch!(edges, left), edges) ++
      derivation_base_path(Map.fetch!(edges, right), edges)
  end

  defp verify_identity(env, members, candidate) do
    cond do
      candidate.members != members ->
        invalid(:member_mismatch, expected: members, submitted: candidate.members)

      true ->
        Enum.reduce_while(members, :ok, fn member, :ok ->
          summary = Env.direct_call_summary(env, member)

          cond do
            is_nil(summary) ->
              {:halt, invalid(:missing_direct_summary, definition: member)}

            candidate.direct_summary_hashes[member] != summary.summary_hash ->
              {:halt, invalid(:summary_hash_mismatch, definition: member)}

            candidate.member_body_hashes[member] != summary.body_hash ->
              {:halt, invalid(:body_hash_mismatch, definition: member)}

            true ->
              {:cont, :ok}
          end
        end)
    end
  end

  defp expected_base_keys(env, members) do
    member_set = MapSet.new(members)

    keys =
      members
      |> Enum.flat_map(fn source ->
        for call <- Env.direct_call_summary(env, source).calls,
            MapSet.member?(member_set, call.callee) do
          {source, call.callee, SizeChange.sparse(call.matrix)}
        end
      end)
      |> Enum.uniq()
      |> Enum.sort()

    {:ok, keys}
  end

  defp verify_base_keys(candidate, expected) do
    if candidate.base_keys == expected,
      do: :ok,
      else: invalid(:base_edge_mismatch, expected: expected, submitted: candidate.base_keys)
  end

  defp verify_base_derivations(candidate, expected) do
    Enum.reduce_while(expected, :ok, fn key, :ok ->
      id = edge_id(key)

      case Map.get(candidate.edges, id) do
        %{source: source, target: target, matrix: matrix, derivation: {:base, ^key}}
        when {source, target, matrix} == key ->
          {:cont, :ok}

        nil ->
          {:halt, invalid(:missing_base_derivation, edge: id, key: key)}

        _other ->
          {:halt, invalid(:invalid_base_derivation, edge: id, key: key)}
      end
    end)
  end

  defp verify_derivations(candidate, base_keys) do
    base_set = MapSet.new(base_keys)

    Enum.reduce_while(Map.keys(candidate.edges), {:ok, %{}}, fn id, {:ok, memo} ->
      case verify_edge(id, candidate.edges, base_set, memo, MapSet.new()) do
        {:ok, next_memo} -> {:cont, {:ok, next_memo}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, _memo} -> :ok
      error -> error
    end
  end

  defp verify_edge(id, edges, base_set, memo, visiting) do
    cond do
      Map.has_key?(memo, id) ->
        {:ok, memo}

      MapSet.member?(visiting, id) ->
        invalid(:cyclic_derivation, edge: id)

      true ->
        case Map.fetch(edges, id) do
          :error ->
            invalid(:unknown_parent_edge, edge: id)

          {:ok, edge} ->
            key = {edge.source, edge.target, edge.matrix}

            if edge_id(key) != id do
              invalid(:edge_id_mismatch, edge: id)
            else
              verify_edge_derivation(edge, edges, base_set, memo, MapSet.put(visiting, id))
            end
        end
    end
  end

  defp verify_edge_derivation(%{id: id, derivation: {:base, key}} = edge, _edges, base_set, memo, _visiting) do
    if key == {edge.source, edge.target, edge.matrix} and MapSet.member?(base_set, key),
      do: {:ok, Map.put(memo, id, true)},
      else: invalid(:invalid_base_derivation, edge: id)
  end

  defp verify_edge_derivation(
         %{id: id, derivation: {:compose, left_id, right_id}} = edge,
         edges,
         base_set,
         memo,
         visiting
       ) do
    with {:ok, memo} <- verify_edge(left_id, edges, base_set, memo, visiting),
         {:ok, memo} <- verify_edge(right_id, edges, base_set, memo, visiting),
         {:ok, composed} <- compose(Map.fetch!(edges, left_id), Map.fetch!(edges, right_id)),
         true <- same_edge?(edge, composed) do
      {:ok, Map.put(memo, id, true)}
    else
      :incompatible -> invalid(:incompatible_composition, edge: id, left: left_id, right: right_id)
      false -> invalid(:composition_mismatch, edge: id, left: left_id, right: right_id)
      {:error, _} = error -> error
    end
  end

  defp verify_edge_derivation(%{id: id}, _edges, _base_set, _memo, _visiting),
    do: invalid(:unknown_derivation, edge: id)

  defp verify_saturation(candidate) do
    edges = Map.values(candidate.edges)
    keys = MapSet.new(edges, &{&1.source, &1.target, &1.matrix})
    by_source = Enum.group_by(edges, & &1.source)

    Enum.reduce_while(edges, :ok, fn left, :ok ->
      Enum.reduce_while(Map.get(by_source, left.target, []), :ok, fn right, :ok ->
        case SizeChange.compose_edges(left, right) do
          {:ok, composed} ->
            key = {composed.source, composed.target, composed.matrix}

            if MapSet.member?(keys, key) do
              {:cont, :ok}
            else
              {:halt,
               invalid(:closure_not_saturated,
                 source: composed.source,
                 target: composed.target,
                 left: left.id,
                 right: right.id
               )}
            end

          :incompatible ->
            {:halt, invalid(:incompatible_dimensions, left: left.id, right: right.id)}
        end
      end)
      |> case do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp compose(left, right), do: SizeChange.compose_edges(left, right)

  defp same_edge?(left, right),
    do: left.source == right.source and left.target == right.target and left.matrix == right.matrix

  defp edge_id(key), do: :crypto.hash(:sha256, :erlang.term_to_binary(key, [:deterministic]))

  defp invalid(reason, details) do
    {:error, {:totality_derivation_invalid, details |> Map.new() |> Map.put(:reason, reason)}}
  end
end
