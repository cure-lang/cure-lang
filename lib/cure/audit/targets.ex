defmodule Cure.Audit.Targets do
  @moduledoc """
  Which BEAM modules are absent on which target VM.

  Hand-maintained data. The ledger already knows every axiom's target MFA, so
  this table is all that stands between it and a portability report. A wrong
  entry yields a wrong report and nothing worse.

  Sources: the AtomVM dead-ends enumerated in `esp32-beam/CLAUDE.md`.
  """

  @unavailable %{
    atomvm:
      MapSet.new([
        :re,
        :inets,
        :httpc,
        :persistent_term,
        :"Elixir.Registry"
      ])
  }

  @spec known() :: [atom()]
  def known, do: @unavailable |> Map.keys() |> Enum.sort()

  @spec unavailable(atom()) :: MapSet.t(atom())
  def unavailable(target), do: Map.get(@unavailable, target, MapSet.new())

  @spec unavailable?(atom(), {atom(), atom(), non_neg_integer()}) :: boolean()
  def unavailable?(target, {m, _f, _a}), do: MapSet.member?(unavailable(target), m)
end
