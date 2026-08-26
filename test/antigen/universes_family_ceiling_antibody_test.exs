defmodule Antigen.UniversesFamilyCeilingAntibodyTest do
  @moduledoc """
  Antigen antibody for the family-level universe ceiling: `Kernel.check_family`
  must reject a family declared at `Type k > ceiling`, not only validate its
  parameter/index telescopes. The pre-fix `check_family` skipped the level
  range-check entirely, so an over-ceiling family was admitted.

  Antigen missed this because the universes vertical exercised the ceiling only
  through def-shaped probes (`ceiling(:ill_typed)` → `check_def`); no family-shaped
  probe declared a family above the ceiling, so the `check_family` range-check had
  zero coverage. `family_ceiling(:ill_typed)` closes that gap.

  Obligations:
    * ORACLE/DISCRIMINATION — `check_family` rejects at `ceiling + 1`
      (`:universe_ceiling`) and accepts at `ceiling`. The two arms are the
      discrimination: a check that never inspected the level would accept both.
    * ASSAY — the universes `:family` assay replays the probe to `:ok` (the kernel
      correctly rejects the `:ill_typed` family).
  """
  use ExUnit.Case, async: true
  alias Antigen.Assays.Universes, as: Assay
  alias Antigen.Generators.Universes, as: Gen
  alias Cure.Core.{Env, Inductive, Kernel, Universe}

  defp check_at(level) do
    Kernel.check_family(Env.empty(), Inductive.family(:Over, [], [], level))
  end

  test "check_family rejects above the ceiling and accepts at it (the discrimination)" do
    assert {:error, :universe_ceiling} == check_at(Universe.ceiling() + 1)
    assert :ok == check_at(Universe.ceiling())
  end

  test "the family_ceiling antibody is labeled :ill_typed and replays :ok" do
    c = Gen.family_ceiling(:ill_typed)
    assert c.label == :ill_typed
    assert c.payload.family.level == Universe.ceiling() + 1
    assert :ok == Assay.run(c)
  end
end
