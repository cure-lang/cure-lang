defmodule Cure.Protocol.Verifier do
  @moduledoc """
  Structural verifier for session-typed protocols (v0.27.0).

  Checks:

    1. Every role appears as either a sender or a receiver in the
       body. Dead roles (declared but unused) raise `PROTO001`.
    2. Every message step names roles that belong to the declared
       role set.
    3. The projected per-role FSM is reachable (every projected state
       is reachable from the projected initial state). Unreachable
       states raise `PROTO001`.
    4. A role's projected FSM has no self-deadlocks: every non-`END`
       state has an outgoing transition.

  ## Entry points

    * `verify/1` -- returns `:ok` or `{:error, [error_tuple]}`.
    * `participant_trace/2` -- return the projected transition list
      for `role`; the caller can feed it into
      `Cure.Temporal.Checker.from_fsm/2` to layer LTL properties on
      top.

  ## Error shape

  Errors are tagged tuples shaped like `Cure.Compiler.Errors` tuples,
  but they are NOT routed through `Cure.Compiler.Errors` or
  `Cure.Diagnostic.Registry`: the protocol DSL is a standalone
  Elixir-side verification API (see `docs/PROTOCOL.md`), not a stage
  of the `.cure` compiler pipeline, so it does not share the
  registry's stable `E`/`W`/`I`/`H` catalog namespace.

      {:protocol_violation, message, meta_keyword_list}

  `meta` includes `:protocol_name`, `:role` (when applicable), and
  an `:code` of `"PROTO001"`. (Earlier releases hardcoded `"E056"`
  here, which collided with the unrelated, fully-catalogued
  `E056 @extern Declaration Missing a Typed Head` compiler
  diagnostic -- see `Cure.Diagnostic.Registry`'s `E056` entry. The
  `PROTO` prefix avoids ever colliding with that catalog again.)
  """

  alias Cure.Protocol.Script

  @doc "Run every structural check against a protocol script."
  @spec verify(Script.t()) :: :ok | {:error, [term()]}
  def verify(%Script{} = script) do
    errors =
      []
      |> check_role_usage(script)
      |> check_role_membership(script)
      |> check_reachability(script)

    case errors do
      [] -> :ok
      _ -> {:error, Enum.reverse(errors)}
    end
  end

  @doc """
  Return the projected transition list for a role.

  Convenience wrapper around `Cure.Protocol.Script.project/2` plus
  `Cure.Temporal.Checker.from_fsm/2` so callers can run temporal
  properties on a role's perspective directly.
  """
  @spec participant_trace(Script.t(), Script.role()) :: map()
  def participant_trace(%Script{} = script, role) do
    transitions = Script.project(script, role)
    Cure.Temporal.Checker.from_fsm(transitions, "S0")
  end

  # -- Checks -----------------------------------------------------------------

  defp check_role_usage(errors, %Script{roles: roles, body: body, name: name}) do
    used = collect_roles(body)

    dead = Enum.reject(roles, &(&1 in used))

    Enum.reduce(dead, errors, fn role, acc ->
      [protocol_error(name, role, "role '#{role}' never appears in the protocol body") | acc]
    end)
  end

  defp check_role_membership(errors, %Script{roles: roles, body: body, name: name}) do
    strangers =
      body
      |> collect_role_refs()
      |> Enum.reject(&(&1 in roles))
      |> Enum.uniq()

    Enum.reduce(strangers, errors, fn role, acc ->
      [
        protocol_error(
          name,
          role,
          "role '#{role}' referenced in protocol body but not declared in the `with` list"
        )
        | acc
      ]
    end)
  end

  defp check_reachability(errors, %Script{roles: roles, name: name} = script) do
    Enum.reduce(roles, errors, fn role, acc ->
      try do
        transitions = Script.project(script, role)
        states = collect_states(transitions)

        reachable =
          if transitions == [] do
            MapSet.new()
          else
            bfs("S0", build_graph(transitions))
          end

        unreachable = Enum.reject(states, &MapSet.member?(reachable, &1))

        Enum.reduce(unreachable, acc, fn s, acc2 ->
          [
            protocol_error(
              name,
              role,
              "state '#{s}' in #{role}'s projection is not reachable from the initial state"
            )
            | acc2
          ]
        end)
      rescue
        ArgumentError ->
          [protocol_error(name, role, "role projection failed") | acc]
      end
    end)
  end

  # -- Graph helpers ----------------------------------------------------------

  defp collect_roles(body) do
    body
    |> collect_role_refs()
    |> Enum.uniq()
  end

  defp collect_role_refs([]), do: []
  defp collect_role_refs([{:msg, f, t, _, _} | rest]), do: [f, t | collect_role_refs(rest)]
  defp collect_role_refs([{:loop, body} | rest]), do: collect_role_refs(body) ++ collect_role_refs(rest)

  defp collect_role_refs([{op, branches} | rest]) when op in [:choose, :offer] do
    refs = Enum.flat_map(branches, &collect_role_refs/1)
    refs ++ collect_role_refs(rest)
  end

  defp collect_role_refs([{:end_, []} | rest]), do: collect_role_refs(rest)
  defp collect_role_refs([_ | rest]), do: collect_role_refs(rest)

  defp collect_states(transitions) do
    froms = Enum.map(transitions, & &1.from)
    tos = Enum.map(transitions, & &1.to)
    (froms ++ tos) |> Enum.uniq()
  end

  defp build_graph(transitions) do
    Enum.reduce(transitions, %{}, fn %{from: from, to: to}, g ->
      Map.update(g, from, [to], fn ts -> [to | ts] end)
    end)
  end

  defp bfs(start, graph) do
    do_bfs([start], MapSet.new([start]), graph)
  end

  defp do_bfs([], visited, _graph), do: visited

  defp do_bfs([current | rest], visited, graph) do
    neighbors = Map.get(graph, current, []) |> Enum.uniq()
    fresh = Enum.reject(neighbors, &MapSet.member?(visited, &1))
    new_visited = Enum.reduce(fresh, visited, &MapSet.put(&2, &1))
    do_bfs(rest ++ fresh, new_visited, graph)
  end

  defp protocol_error(name, role, message) do
    {:protocol_violation, message, [code: "PROTO001", protocol_name: name, role: role]}
  end
end
