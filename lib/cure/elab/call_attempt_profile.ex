defmodule Cure.Elab.CallAttemptProfile do
  @moduledoc """
  Scoped aggregation of speculative elaboration attempts.

  The elaborator is deliberately oblivious to benchmark ownership: recording is
  a no-op unless `run/1` has installed a process-local profile. Each attempt is
  grouped by its authored call identity, candidate, strategy, and outcome. This
  keeps profiling memory proportional to the number of distinct paths rather
  than to the (potentially very large) number of retries.
  """

  @attempts_key {__MODULE__, :attempts}
  @call_key {__MODULE__, :call}
  @metrics_key {__MODULE__, :metrics}

  @type call_identity :: %{
          required(:declaration) => atom() | String.t() | nil,
          required(:span) => term(),
          required(:callee) => String.t(),
          required(:expected_type) => term()
        }

  @type attempt :: map()

  @doc "Run `fun` with a fresh attempt aggregate and return `{result, attempts}`."
  @spec run((-> result)) :: {result, [attempt()]} when result: term()
  def run(fun) when is_function(fun, 0) do
    previous_attempts = Process.put(@attempts_key, %{})
    previous_call = Process.get(@call_key)
    previous_metrics = Process.put(@metrics_key, %{})
    Process.delete(@call_key)

    try do
      result = fun.()

      attempts =
        @attempts_key
        |> Process.get(%{})
        |> Enum.map(fn {identity, count} -> Map.put(identity, :count, count) end)
        |> Enum.sort_by(&sort_key/1)

      {result, attempts}
    after
      restore(@attempts_key, previous_attempts)
      restore(@call_key, previous_call)
      restore(@metrics_key, previous_metrics)
    end
  end

  @doc "Increment an operation-local counter when profiling is active."
  @spec increment(atom(), non_neg_integer()) :: :ok
  def increment(name, amount \\ 1) when is_atom(name) and is_integer(amount) and amount >= 0 do
    case Process.get(@metrics_key) do
      metrics when is_map(metrics) ->
        Process.put(@metrics_key, Map.update(metrics, name, amount, &(&1 + amount)))
        :ok

      _ ->
        :ok
    end
  end

  @doc "Return operation-local counters for the current profiling scope."
  @spec metrics() :: %{optional(atom()) => non_neg_integer()}
  def metrics, do: Process.get(@metrics_key, %{})

  @doc "Return the counter delta from a previously captured metrics map."
  @spec delta(%{optional(atom()) => non_neg_integer()}) :: %{optional(atom()) => non_neg_integer()}
  def delta(previous) when is_map(previous) do
    current = metrics()

    current
    |> Map.keys()
    |> Kernel.++(Map.keys(previous))
    |> Enum.uniq()
    |> Enum.reduce(%{}, fn name, delta ->
      amount = max(Map.get(current, name, 0) - Map.get(previous, name, 0), 0)
      if amount == 0, do: delta, else: Map.put(delta, name, amount)
    end)
  end

  @doc "Associate attempts made by `fun` with one authored call site."
  @spec with_call(call_identity(), (-> result)) :: result when result: term()
  def with_call(call, fun) when is_map(call) and is_function(fun, 0) do
    if active?() do
      previous = Process.get(@call_key)

      call =
        case previous do
          %{span: span, callee: callee, expected_type: expected}
          when span == call.span and callee == call.callee and call.expected_type == :inference ->
            Map.put(call, :expected_type, expected)

          _ ->
            call
        end

      Process.put(@call_key, call)

      try do
        fun.()
      after
        restore(@call_key, previous)
      end
    else
      fun.()
    end
  end

  @doc "Execute and, when profiling is active, count one candidate strategy."
  @spec attempt(term(), atom(), (-> result)) :: result when result: term()
  def attempt(candidate, strategy, fun) when is_atom(strategy) and is_function(fun, 0) do
    result = fun.()

    with %{} = attempts <- Process.get(@attempts_key),
         %{} = call <- Process.get(@call_key) do
      identity =
        call
        |> Map.put(:candidate, candidate)
        |> Map.put(:strategy, strategy)
        |> Map.put(:outcome, outcome(result))

      Process.put(@attempts_key, Map.update(attempts, identity, 1, &(&1 + 1)))
    else
      _ -> :ok
    end

    result
  end

  @doc "Whether the current process is inside `run/1`."
  @spec active?() :: boolean()
  def active?, do: is_map(Process.get(@attempts_key))

  defp outcome({:ok, _term, _type}), do: :success
  defp outcome({:ok, _value}), do: :success
  defp outcome({:error, reason}), do: {:error, reason_tag(reason)}
  defp outcome(other), do: {:result, result_tag(other)}

  defp reason_tag({:source_context, reason, _context}), do: reason_tag(reason)
  defp reason_tag({tag, _rest}) when is_atom(tag), do: tag
  defp reason_tag({tag, _, _}) when is_atom(tag), do: tag
  defp reason_tag({tag, _, _, _}) when is_atom(tag), do: tag
  defp reason_tag(tag) when is_atom(tag), do: tag
  defp reason_tag(_), do: :other

  defp result_tag(value) when is_tuple(value) and tuple_size(value) > 0, do: elem(value, 0)
  defp result_tag(value), do: value

  defp sort_key(attempt) do
    {
      inspect(Map.get(attempt, :declaration)),
      inspect(Map.get(attempt, :span)),
      Map.get(attempt, :callee, ""),
      inspect(Map.get(attempt, :expected_type)),
      inspect(Map.get(attempt, :candidate)),
      inspect(Map.get(attempt, :strategy)),
      inspect(Map.get(attempt, :outcome))
    }
  end

  defp restore(key, nil), do: Process.delete(key)
  defp restore(key, value), do: Process.put(key, value)
end
