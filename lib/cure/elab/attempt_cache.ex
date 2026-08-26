defmodule Cure.Elab.AttemptCache do
  @moduledoc """
  Operation-local cache for untrusted elaboration attempts.

  The cache is deliberately process-local and scoped. It is never published in
  an interface, included in an environment hash, or consulted by the kernel.
  Callers use `scope/1` around one declaration/program operation; nested scopes
  reuse the parent's state and restore it on exit.
  """

  @key {__MODULE__, :state}

  @type kind :: :blocked | :normalize | :defeq
  @type state :: %{optional(kind()) => map()}

  @spec scope((-> result)) :: result when result: term()
  def scope(fun) when is_function(fun, 0) do
    case Process.get(@key) do
      state when is_map(state) ->
        fun.()

      _ ->
        previous = Process.put(@key, empty_state())

        try do
          fun.()
        after
          restore(previous)
        end
    end
  end

  @spec fetch(kind(), term(), (-> value)) :: {:hit, value} | {:miss, value}
        when value: term()
  def fetch(kind, key, fun) when is_atom(kind) and is_function(fun, 0) do
    case Process.get(@key) do
      %{^kind => cache} when is_map(cache) ->
        case Map.fetch(cache, key) do
          {:ok, value} -> {:hit, value}
          :error -> store_and_miss(kind, key, fun.())
        end

      _ ->
        {:miss, fun.()}
    end
  end

  @spec get(kind(), term()) :: {:ok, term()} | :miss
  def get(kind, key) when is_atom(kind) do
    case Process.get(@key) do
      %{^kind => cache} when is_map(cache) -> Map.fetch(cache, key)
      _ -> :miss
    end
  end

  @spec put(kind(), term(), term()) :: :ok
  def put(kind, key, value) when is_atom(kind) do
    case Process.get(@key) do
      %{^kind => cache} = state when is_map(cache) ->
        Process.put(@key, Map.put(state, kind, Map.put(cache, key, value)))
        :ok

      _ ->
        :ok
    end
  end

  @spec active?() :: boolean()
  def active?, do: is_map(Process.get(@key))

  defp empty_state, do: %{blocked: %{}, normalize: %{}, defeq: %{}}

  defp store_and_miss(kind, key, value) do
    put(kind, key, value)
    {:miss, value}
  end

  defp restore(nil), do: Process.delete(@key)
  defp restore(previous), do: Process.put(@key, previous)
end
