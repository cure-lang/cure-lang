defmodule Cure.Stdlib.GroupPlacementTest do
  @moduledoc """
  Every stdlib source that declares `@group(:g)` places it ABOVE its `mod`
  line, not inside the body (spec 2026-07-10-group-decorator-placement). This
  is the migration guard: it goes red if any file keeps the legacy in-body
  placement.
  """
  use ExUnit.Case, async: true

  @std_dir Path.join([File.cwd!(), "lib", "std"])

  test "no stdlib file has @group inside the mod body" do
    offenders =
      @std_dir
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.filter(&group_below_mod?/1)

    assert offenders == [],
           "these stdlib files still have @group inside the mod body: " <>
             Enum.map_join(offenders, ", ", &Path.basename/1)
  end

  # True iff the file's `@group(` line appears AFTER its `mod ` line.
  defp group_below_mod?(path) do
    lines = path |> File.read!() |> String.split("\n")
    group_idx = Enum.find_index(lines, &(&1 =~ ~r/^\s*@group\(/))
    mod_idx = Enum.find_index(lines, &(&1 =~ ~r/^\s*mod\s/))
    group_idx != nil and mod_idx != nil and group_idx > mod_idx
  end
end
