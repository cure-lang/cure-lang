defmodule Cure.Compiler.ModulePipeline.BodyElaborationTrace do
  @moduledoc """
  Records, during one `Cure.Compiler.ModulePipeline.check/2`, every time
  elaborating one module's bodies required elaborating another module's bodies.

  The interface-first design says this should be rare and deliberate: a module's
  bodies are checked against *frozen interfaces*, so the only legitimate case is
  a mutually recursive component, whose members are checked together by
  construction. Everything else — reaching for a provider's source to construct
  ambient scope, elaborating a provider to answer a prelude question — is the
  failure mode the previous pipeline had, and it is invisible unless something
  counts it.

  So this counts it. The trace is process-local because a check runs in one
  process and the recording sites are deep inside elaboration, where threading an
  accumulator would mean changing every signature between here and there. It is
  scoped: `run/1` installs a fresh trace and removes it afterwards, so a nested
  or subsequent check never inherits another run's tally.
  """

  @key {__MODULE__, :events}

  @type event :: %{source: String.t(), target: String.t(), phase: atom()}

  @doc "Run `fun` with a fresh trace installed; returns `{result, events}`."
  @spec run((-> result)) :: {result, [event()]} when result: term()
  def run(fun) when is_function(fun, 0) do
    previous = Process.put(@key, [])

    try do
      result = fun.()
      {result, Process.get(@key, []) |> Enum.reverse()}
    after
      if previous, do: Process.put(@key, previous), else: Process.delete(@key)
    end
  end

  @doc """
  Note that checking `source`'s bodies elaborated `target`'s bodies.

  A no-op outside a `run/1` scope, so recording sites can be unconditional.
  """
  @spec record(String.t(), String.t()) :: :ok
  def record(source, target) when is_binary(source) and is_binary(target) do
    case Process.get(@key) do
      nil -> :ok
      events -> Process.put(@key, [%{source: source, target: target, phase: phase()} | events]) && :ok
    end
  end

  # The parser sets `:cure_loading_prelude` for the whole time the prelude's own
  # sources are being read, which is precisely the window in which a provider
  # body elaboration would mean the prelude is being bootstrapped by compiling
  # providers rather than by reading their interfaces.
  defp phase do
    if Process.get(:cure_loading_prelude), do: :during_prelude_bootstrap, else: :check_bodies
  end
end
