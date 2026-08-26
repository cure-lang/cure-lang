defmodule Antigen.ReplayRegistryTest do
  @moduledoc """
  `Antigen.Runner.replay_registry/0` — the full assay id → module map, built from
  the authoritative dispatch table so it covers every registered assay (unlike the
  hardcoded subset in `corpus_replay_test`). This is the registry `Antigen.Prune`
  re-checks corpus records against.
  """
  use ExUnit.Case, async: true
  alias Antigen.Runner

  test "covers every registered assay and every value is a run/1 module" do
    reg = Runner.replay_registry()

    assert Enum.sort(Map.keys(reg)) == Enum.sort(Runner.registered_assays())
    assert map_size(reg) == length(Runner.registered_assays())

    for {_id, mod} <- reg do
      Code.ensure_loaded!(mod)
      assert function_exported?(mod, :run, 1)
    end

    # spot-check one known wiring against the dispatch table
    assert reg["totality/diverging"] == Antigen.Assays.Totality
  end
end
