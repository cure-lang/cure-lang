defmodule Antigen.RegenTest do
  @moduledoc """
  `Antigen.Regen.regenerate_seeds/1` — drop the stale seed pool and re-harvest
  coverage-novel seeds from the current generators into a fresh file, atomically
  replacing the old one. The regenerated pool must decode and replay clean. All I/O
  is on a tmp destination (the committed store is never touched).
  """
  use ExUnit.Case, async: true
  alias Antigen.{Regen, Runner}

  @tmp "tmp/antigen_regen_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "replaces (not appends) with a fresh, decodable, replay-clean pool" do
    dest = Path.join(@tmp, "seeds.sexp")
    File.write!(dest, "stale garbage line that must not survive\n")

    result =
      Regen.regenerate_seeds(
        seeds_path: dest,
        count: 60,
        gen: Antigen.Generators.Totality.gen()
      )

    assert result.dest == dest
    assert result.seeds_banked > 0

    # replace, not append: the stale line is gone
    refute File.read!(dest) =~ "stale garbage line"

    # every regenerated record decodes and replays :ok through the live kernel
    results = Runner.replay([dest], Runner.replay_registry())
    assert results != []
    assert Enum.all?(results, &(&1.verdict == :ok))
  end
end
