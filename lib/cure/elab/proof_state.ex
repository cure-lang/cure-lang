defmodule Cure.Elab.ProofState do
  @moduledoc """
  Untrusted, process-local observations of proof commands and checked holes.

  Capture is scoped to one elaboration and restored even on exceptions. States
  are presentation data, never evidence or inputs to the kernel. Failed
  elaborations retain observations made before the failure.

  The custom LSP proof-state request and REPL goal view use this source-indexed
  API through an explicit `SourceContext`. Legacy `Program.hole_goals/1` is a
  coarse definition-return compatibility summary, not a nested-hole obligation.
  """

  alias Cure.Core.{Env, Printer}
  alias Cure.Diagnostic.Span
  alias Cure.Elab.{Name, ProofGoal}
  alias Cure.MetaAST.Metadata
  alias Cure.Pipeline.Events

  @capture_key {__MODULE__, :capture}
  @rendering_key {__MODULE__, :rendering}
  @command_key {__MODULE__, :command}
  @session_key {__MODULE__, :session}
  @session_scope_key {__MODULE__, :session_scope}
  @statement_key {__MODULE__, :statement}
  @speculating_key {__MODULE__, :speculating}

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
  def speculate(fun) do
    if active?() do
      previous = Process.put(@speculating_key, true)

      try do
        capture(fun)
      after
        restore(@speculating_key, previous)
      end
    else
      {fun.(), []}
    end
  end

  @doc false
  def commit_observations(states) do
    Enum.each(states, &record/1)
  end

  @doc false
  def with_session(fun, source \\ nil) do
    previous = Process.put(@session_key, true)
    previous_scope = Process.get(@session_scope_key)

    if source do
      scope = authored_span(span(source), Process.get(@statement_key) || previous_scope)
      Process.put(@session_scope_key, scope)
    end

    try do
      fun.()
    after
      restore(@session_key, previous)
      restore(@session_scope_key, previous_scope)
    end
  end

  @doc false
  def within_statement(statement, fun) do
    previous = Process.get(@statement_key)
    current = authored_span(span(statement), previous || Process.get(@session_scope_key))
    Process.put(@statement_key, current || previous)

    try do
      fun.()
    after
      restore(@statement_key, previous)
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
    {result, context} = Cure.Elab.SourceContext.analyze(source, opts)
    {result, context.observations}
  end

  @doc false
  def observe(phase, statement, original, goals) do
    if active?() and not Process.get(@session_key, false) do
      scope = span(original.source)

      record(%{
        id: original.id,
        phase: phase,
        kind: :command,
        span: authored_span(span(statement), scope),
        scope: scope,
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

  @doc "Observe the entire source-session frontier without retaining proof evidence."
  def observe_session(phase, statement, root, frontier) do
    if active?() do
      root_span = span(root.source)
      authored = Process.get(@statement_key) || Process.get(@session_scope_key) || root_span
      statement_span = authored_span(span(statement), authored)
      scope = authored_span(Process.get(@session_scope_key) || hull(root_span, statement_span), authored)

      record(%{
        id: {:session, root.id},
        phase: phase,
        kind: :session,
        span: statement_span,
        scope: scope,
        goals: Enum.map(frontier, &view/1)
      })
    end

    :ok
  end

  @doc "Return the latest authoritative frontiers and standalone hole goals."
  def remaining(snapshots) do
    latest = snapshots |> Enum.reverse() |> Enum.uniq_by(& &1.id) |> Enum.reverse()
    indexed = Enum.with_index(latest)
    sessions = Enum.filter(indexed, fn {state, _index} -> state.kind == :session end)

    indexed
    |> Enum.reject(fn {state, index} ->
      Enum.any?(sessions, fn {session, session_index} ->
        session.id != state.id and state.kind != :hole and
          contains_span?(session.scope, state.scope || state.span) and
          (state.kind != :session or span_size(session.scope) > span_size(state.scope) or session_index > index)
      end)
    end)
    |> Enum.flat_map(fn {state, _index} -> state.goals end)
    |> Enum.uniq_by(& &1.id)
  end

  @doc "Select the proof state at an LSP position using the negotiated encoding."
  def at(snapshots, source, position, encoding \\ :utf16) do
    cursor = {Map.get(position, "line", 0), Map.get(position, "character", 0)}

    relevant =
      Enum.filter(snapshots, fn state ->
        inside?(state.scope || state.span, source, encoding, cursor)
      end)

    relevant =
      case Enum.min_by(relevant, &span_size(&1.scope || &1.span), fn -> nil end) do
        nil ->
          []

        inner ->
          size = span_size(inner.scope || inner.span)
          Enum.filter(relevant, &(span_size(&1.scope || &1.span) == size))
      end

    # Inside a command, show its input. At its end (or between commands), show
    # its output. This gives precise before/after semantics on a single line.
    case Enum.find(Enum.sort_by(relevant, &span_size(&1.span)), fn state ->
           state.phase == :before and inside_command?(state.span, source, encoding, cursor)
         end) do
      nil ->
        relevant
        |> Enum.reject(&(&1.phase == :before))
        |> Enum.filter(fn state ->
          (state.kind == :hole and inside?(state.span, source, encoding, cursor)) or
            range_end(state.span, source, encoding) <= cursor
        end)
        |> Enum.sort_by(fn state -> -span_size(state.scope || state.span) end)
        |> List.last()
        |> case do
          nil ->
            case relevant |> Enum.sort_by(&span_size(&1.scope || &1.span)) |> List.first() do
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

    unless Process.get(@speculating_key, false) do
      location = state.span || state.scope
      file = if location, do: location.path || location.source_id, else: "nofile"
      line = if location, do: location.start_line, else: 1
      Events.emit(:type_checker, :proof_state, state, %{file: file, line: line})
    end
  end

  defp span({_tag, meta, children}), do: hull(span(meta), span(children))

  defp span(meta) when is_list(meta) do
    if Keyword.keyword?(meta) do
      case Metadata.source_info(meta) do
        %{whole: %Span{} = whole} -> whole
        _ -> nil
      end
    else
      Enum.reduce(meta, nil, &hull(span(&1), &2))
    end
  end

  defp span(_other), do: nil

  defp hull(nil, span), do: span
  defp hull(span, nil), do: span

  defp hull(%Span{} = left, %Span{} = right) do
    if same_source?(left, right) do
      first = if left.start_byte <= right.start_byte, do: left, else: right
      last = if left.end_byte >= right.end_byte, do: left, else: right
      %{first | end_byte: last.end_byte, end_line: last.end_line, end_column: last.end_column}
    else
      left
    end
  end

  defp authored_span(nil, _anchor), do: nil
  defp authored_span(span, nil), do: span
  defp authored_span(span, anchor), do: if(same_source?(span, anchor), do: span, else: anchor)

  defp same_source?(%Span{} = left, %Span{} = right) do
    identity = left.path || left.source_id
    not is_nil(identity) and identity == (right.path || right.source_id)
  end

  defp contains_span?(%Span{} = outer, %Span{} = inner),
    do: same_source?(outer, inner) and outer.start_byte <= inner.start_byte and inner.end_byte <= outer.end_byte

  defp contains_span?(_outer, _inner), do: false

  defp span_size(%Span{start_byte: first, end_byte: last}), do: last - first
  defp span_size(nil), do: 1_000_000_000

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
