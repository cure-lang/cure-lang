defmodule Cure.Core.SCCCertificate do
  @moduledoc """
  Trusted verifier for an untrusted definition-SCC proposal.

  Agda computes SCCs in its recursivity checker before `termMutual'`. Cure has a
  smaller explicit kernel boundary, so this module checks a condensation-order
  and two-tree certificate against trusted direct-call summaries. It performs
  no SCC search and never scans Core bodies.
  """

  alias Cure.Core.Env

  @partition_version 1

  @spec verify_partition(Env.t(), map()) :: {:ok, [[atom()]]} | {:error, term()}
  def verify_partition(%Env{} = env, %{version: @partition_version} = certificate) do
    started = System.monotonic_time(:microsecond)

    result =
      with :ok <- verify_universe(env, certificate),
           {:ok, expected_edges} <- verify_edge_completeness(env, certificate),
           :ok <- verify_submitted_edges(certificate, expected_edges),
           :ok <- verify_partition_totality(certificate),
           :ok <- verify_ranks(certificate, expected_edges),
           :ok <- verify_components(certificate, expected_edges) do
        components =
          certificate.components
          |> Map.values()
          |> Enum.map(& &1.members)
          |> Enum.sort()

        {:ok, components}
      end

    emit_metric(certificate, result, started)
    result
  end

  def verify_partition(_env, certificate) do
    {:error, {:totality_scc_invalid, %{reason: :unsupported_version, version: Map.get(certificate, :version)}}}
  end

  defp emit_metric(certificate, result, started) do
    Cure.Pipeline.Events.emit(
      :kernel,
      :totality_metric,
      %{
        operation: :partition_verification,
        definitions: length(Map.get(certificate, :universe, [])),
        components: map_size(Map.get(certificate, :components, %{})),
        direct_edges: length(Map.get(certificate, :edges, [])),
        result: if(match?({:ok, _}, result), do: :ok, else: :error),
        elapsed_us: System.monotonic_time(:microsecond) - started
      },
      %{}
    )
  end

  defp verify_universe(env, certificate) do
    universe = Map.get(certificate, :universe, [])

    cond do
      universe != Enum.sort(Enum.uniq(universe)) ->
        invalid(:noncanonical_universe)

      true ->
        Enum.reduce_while(universe, :ok, fn name, :ok ->
          case {Env.get_def(env, name), Env.direct_call_summary(env, name),
                get_in(certificate, [:summary_hashes, name])} do
            {nil, _, _} ->
              {:halt, invalid(:unknown_definition, definition: name)}

            {_, nil, _} ->
              {:halt, invalid(:missing_direct_summary, definition: name)}

            {_, %{summary_hash: actual}, actual} ->
              {:cont, :ok}

            {_, %{summary_hash: actual}, submitted} ->
              {:halt, {:error, {:totality_summary_stale, %{definition: name, expected: actual, submitted: submitted}}}}
          end
        end)
    end
  end

  defp verify_edge_completeness(env, certificate) do
    universe = MapSet.new(certificate.universe)

    Enum.reduce_while(certificate.universe, {:ok, []}, fn source, {:ok, edges} ->
      summary = Env.direct_call_summary(env, source)

      summary.calls
      |> Enum.with_index()
      |> Enum.reduce_while({:ok, edges}, fn {call, ordinal}, {:ok, acc} ->
        cond do
          MapSet.member?(universe, call.callee) ->
            edge = %{id: {source, call.id, ordinal}, source: source, target: call.callee}
            {:cont, {:ok, [edge | acc]}}

          terminal_boundary?(env, call.callee, certificate) ->
            {:cont, {:ok, acc}}

          true ->
            {:halt,
             {:error,
              {:totality_scc_incomplete,
               %{
                 caller: source,
                 omitted: call.callee,
                 summary_hash: summary.summary_hash
               }}}}
        end
      end)
      |> case do
        {:ok, next} -> {:cont, {:ok, next}}
        {:error, _} = error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, edges} -> {:ok, Enum.sort_by(edges, &{&1.source, &1.target, &1.id})}
      error -> error
    end
  end

  defp terminal_boundary?(env, callee, certificate) do
    case Env.get_def(env, callee) do
      %{body: {:extern, _}} -> true
      %{builtin_op: op} when not is_nil(op) -> true
      _ -> valid_sealed_boundary?(env, callee, certificate)
    end
  end

  defp valid_sealed_boundary?(env, callee, certificate) do
    submitted = Map.get(Map.get(certificate, :sealed_boundaries, %{}), callee)
    expected = Map.get(env.totality_component_of, callee)
    Env.total?(env, callee) and is_binary(expected) and submitted == expected
  end

  defp verify_submitted_edges(certificate, expected) do
    if Map.get(certificate, :edges) == expected,
      do: :ok,
      else: invalid(:direct_edges_mismatch, expected: expected, submitted: Map.get(certificate, :edges))
  end

  defp verify_partition_totality(certificate) do
    universe = MapSet.new(certificate.universe)
    component_of = Map.get(certificate, :component_of, %{})
    components = Map.get(certificate, :components, %{})

    assigned =
      components
      |> Enum.flat_map(fn {id, component} -> Enum.map(component.members, &{&1, id}) end)

    cond do
      MapSet.new(Map.keys(component_of)) != universe ->
        invalid(:partition_domain_mismatch)

      Enum.count(assigned) != MapSet.size(universe) ->
        invalid(:partition_duplicate_member)

      Enum.any?(assigned, fn {member, id} -> Map.get(component_of, member) != id end) ->
        invalid(:component_index_mismatch)

      Enum.any?(components, fn {id, component} ->
        component.members == [] or component.members != Enum.sort(Enum.uniq(component.members)) or
          id != hd(component.members) or component.root != hd(component.members)
      end) ->
        invalid(:noncanonical_component)

      true ->
        :ok
    end
  end

  defp verify_ranks(certificate, edges) do
    ids = Map.keys(certificate.components)
    ranks = Map.get(certificate, :rank, %{})

    cond do
      MapSet.new(Map.keys(ranks)) != MapSet.new(ids) ->
        invalid(:rank_domain_mismatch)

      Enum.sort(Map.values(ranks)) != Enum.to_list(0..(length(ids) - 1)//1) ->
        invalid(:rank_not_total)

      true ->
        Enum.reduce_while(edges, :ok, fn edge, :ok ->
          source = Map.fetch!(certificate.component_of, edge.source)
          target = Map.fetch!(certificate.component_of, edge.target)

          if source == target or Map.fetch!(ranks, source) > Map.fetch!(ranks, target) do
            {:cont, :ok}
          else
            {:halt,
             invalid(:rank_not_decreasing,
               source: edge.source,
               target: edge.target,
               source_component: source,
               target_component: target
             )}
          end
        end)
    end
  end

  defp verify_components(certificate, edges) do
    edge_by_id = Map.new(edges, &{&1.id, &1})

    Enum.reduce_while(certificate.components, :ok, fn {id, component}, :ok ->
      with :ok <- verify_tree(id, component, component.forward_tree, edge_by_id, :forward),
           :ok <- verify_tree(id, component, component.reverse_tree, edge_by_id, :reverse) do
        {:cont, :ok}
      else
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp verify_tree(component_id, component, tree_ids, edge_by_id, direction) do
    expected_count = length(component.members) - 1

    if length(tree_ids) != expected_count do
      invalid(:tree_edge_count,
        component: component_id,
        direction: direction,
        expected: expected_count,
        actual: length(tree_ids)
      )
    else
      walk_tree(component_id, component.root, MapSet.new([component.root]), tree_ids, edge_by_id, direction)
      |> case do
        {:ok, seen} ->
          if seen == MapSet.new(component.members),
            do: :ok,
            else: invalid(:tree_not_spanning, component: component_id, direction: direction)

        {:error, _} = error ->
          error
      end
    end
  end

  defp walk_tree(_component, _root, seen, [], _edges, _direction), do: {:ok, seen}

  defp walk_tree(component, root, seen, [edge_id | rest], edges, direction) do
    case Map.fetch(edges, edge_id) do
      :error ->
        invalid(:unknown_tree_edge, edge: edge_id)

      {:ok, edge} ->
        {from, to} = if direction == :forward, do: {edge.source, edge.target}, else: {edge.target, edge.source}

        cond do
          not MapSet.member?(seen, from) ->
            invalid(:tree_parent_unreached, component: component, edge: edge_id, root: root)

          MapSet.member?(seen, to) ->
            invalid(:tree_cycle, component: component, edge: edge_id)

          true ->
            walk_tree(component, root, MapSet.put(seen, to), rest, edges, direction)
        end
    end
  end

  defp invalid(reason, details \\ []) do
    {:error, {:totality_scc_invalid, details |> Map.new() |> Map.put(:reason, reason)}}
  end
end
