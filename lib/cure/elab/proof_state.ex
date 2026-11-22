defmodule Cure.Elab.ProofState do
  @moduledoc """
  Untrusted, process-local observations of proof commands and checked holes.

  Capture is scoped to one elaboration and restored even on exceptions. States
  are presentation data, never evidence or inputs to the kernel. Failed
  elaborations retain observations made before the failure.

  The custom LSP proof-state request and REPL goal view use this source-indexed
  API. Legacy `Program.hole_goals/1` and the existing hole inlay hints still use
  definition-return summaries, not precise nested-hole obligations. An editor
  goal-panel client is separate from this server-side observation API.
  """

  alias Cure.Core.{Env, Printer}
  alias Cure.Diagnostic.Span
  alias Cure.Elab.{Name, Program, ProofGoal}
  alias Cure.MetaAST.Metadata
  alias Cure.Pipeline.Events

  @capture_key {__MODULE__, :capture}
  @rendering_key {__MODULE__, :rendering}
  @command_key {__MODULE__, :command}

  @doc "Capture observations made by a callback, without changing its return value."
  def capture(fun) when is_function(fun, 0) do
    previous = Process.get(@capture_key)
    Process.put(@capture_key, [])

    try do
      result = fun.()
      {result, @capture_key |> Process.get() |> Enum.reverse()}
    after
      restore(@capture_key, previous)
    end
  end

  @doc false
  def within_command(fun) do
    previous = Process.put(@command_key, true)

    try do
      fun.()
    after
      restore(@command_key, previous)
    end
  end

  @doc false
  def checked_solver({_, meta, _} = command, expected, names, context, env, fun) do
    if Process.get(@command_key, false) or not active?() do
      fun.()
    else
      goal = ProofGoal.new(expected, names, context, env, meta)
      observe(:before, command, goal, [goal])
      result = within_command(fun)

      case result do
        {:ok, _evidence} -> observe(:after, command, goal, [])
        {:error, _reason} -> observe(:failed, command, goal, [goal])
      end

      result
    end
  end

  @doc "Elaborate a buffer and retain partial proof states even if it is refused."
  def elaborate(source, opts \\ []) do
    {result, snapshots} = capture(fn -> Program.elaborate(source, opts) end)
    file = Keyword.get(opts, :file, "nofile")
    {result, Enum.filter(snapshots, &(from_file?(&1.span, file) or from_file?(&1.scope, file)))}
  end

  @doc false
  def observe(phase, statement, original, goals) do
    if active?() do
      record(%{
        id: original.id,
        phase: phase,
        kind: :command,
        span: span(statement),
        scope: span(original.source),
        goals: Enum.map(goals, &view/1)
      })
    end

    :ok
  end

  @doc false
  def hole(id, meta, expected, names, context, env) do
    if active?() do
      goal = ProofGoal.new(expected, names, context, env, meta)

      record(%{
        id: {:hole, id},
        phase: :hole,
        kind: :hole,
        span: span(meta),
        scope: span(meta),
        goals: [%{view(goal) | id: id}]
      })
    end

    :ok
  end

  @doc "Return the last observed remaining goals, in observation order."
  def remaining(snapshots) do
    snapshots
    |> Enum.reverse()
    |> Enum.uniq_by(& &1.id)
    |> Enum.reverse()
    |> Enum.flat_map(& &1.goals)
  end

  @doc "Select the proof state at an LSP position using the negotiated encoding."
  def at(snapshots, source, position, encoding \\ :utf16) do
    cursor = {Map.get(position, "line", 0), Map.get(position, "character", 0)}

    relevant =
      Enum.filter(snapshots, fn state ->
        inside?(state.scope || state.span, source, encoding, cursor)
      end)

    # Inside a command, show its input. At its end (or between commands), show
    # its output. This gives precise before/after semantics on a single line.
    case Enum.find(relevant, fn state ->
           state.phase == :before and inside_command?(state.span, source, encoding, cursor)
         end) do
      nil ->
        relevant
        |> Enum.reject(&(&1.phase == :before))
        |> Enum.filter(fn state ->
          (state.kind == :hole and inside?(state.span, source, encoding, cursor)) or
            range_end(state.span, source, encoding) <= cursor
        end)
        |> List.last()
        |> case do
          nil ->
            case List.first(relevant) do
              %{phase: :before, goals: goals} -> goals
              _ -> []
            end

          state ->
            state.goals
        end

      state ->
        state.goals
    end
  end

  @doc "Render a goal with authored names, including deferred local facts."
  def view(goal) do
    # `have` facts are deferred surface lets, not kernel-context binders.
    # Their inferred types and the target are still scoped by context_names.
    deferred = Enum.count(goal.builders, &match?({:assignment, _, _}, &1))
    names = Enum.drop(goal.names, deferred)
    previous = Process.put(@rendering_key, true)

    try do
      inspection = ProofGoal.inspect_goal(goal)

      hypotheses =
        Enum.map(inspection.hypotheses, fn hypothesis ->
          Map.put(hypothesis, :text, print(hypothesis.type, names))
        end)

      %{
        id: inspect(goal.id),
        function: function_name(goal.env),
        target: inspection.target,
        goal: print(inspection.target, names),
        hypotheses: hypotheses,
        context: Enum.map(hypotheses, &"#{&1.name} : #{&1.text}"),
        status: inspection.status
      }
    after
      restore(@rendering_key, previous)
    end
  end

  defp function_name(env) do
    case Env.current_def(env) do
      nil -> nil
      name -> if Name.owner(name), do: name, else: Name.qualify(Env.owner(env) || "Main", name)
    end
  end

  defp print(:pending, _names), do: "(not yet checked)"

  defp print(term, names) do
    Printer.print(term, names)
  rescue
    ArgumentError -> Cure.Elab.ProofDisplay.format(term, names)
  end

  defp active? do
    not Process.get(@rendering_key, false) and
      (is_list(Process.get(@capture_key)) or subscribed?())
  end

  defp subscribed? do
    Events.emission_enabled?() and
      Enum.any?(Registry.lookup(Cure.Pipeline.Events.Registry, :type_checker), fn {_pid, filter} ->
        filter in [:all, :proof_state]
      end)
  end

  defp record(state) do
    case Process.get(@capture_key) do
      states when is_list(states) -> Process.put(@capture_key, [state | states])
      nil -> :ok
    end

    location = state.span || state.scope
    file = if location, do: location.path || location.source_id, else: "nofile"
    line = if location, do: location.start_line, else: 1
    Events.emit(:type_checker, :proof_state, state, %{file: file, line: line})
  end

  defp span({_tag, meta, _children}), do: span(meta)

  defp span(meta) when is_list(meta) do
    case Metadata.source_info(meta) do
      %{whole: %Span{} = whole} -> whole
      _ -> nil
    end
  end

  defp span(_other), do: nil

  defp from_file?(%Span{source_id: file}, file), do: true
  defp from_file?(%Span{path: file}, file), do: true
  defp from_file?(_span, _file), do: false

  defp inside?(nil, _source, _encoding, _cursor), do: false

  defp inside?(span, source, encoding, cursor) do
    range = Cure.LSP.Positions.range(span, source, encoding)
    point(range["start"]) <= cursor and cursor <= point(range["end"])
  end

  defp inside_command?(nil, _source, _encoding, _cursor), do: false

  defp inside_command?(span, source, encoding, cursor) do
    inside?(span, source, encoding, cursor) and
      cursor < point(Cure.LSP.Positions.range(span, source, encoding)["end"])
  end

  defp range_end(nil, _source, _encoding), do: {0, 0}

  defp range_end(span, source, encoding),
    do: span |> Cure.LSP.Positions.range(source, encoding) |> Map.fetch!("end") |> point()

  defp point(position), do: {position["line"], position["character"]}

  defp restore(key, nil), do: Process.delete(key)
  defp restore(key, value), do: Process.put(key, value)
end
