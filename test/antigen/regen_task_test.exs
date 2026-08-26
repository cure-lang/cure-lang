defmodule Mix.Tasks.Antigen.RegenSeedsTest do
  use ExUnit.Case, async: true
  import ExUnit.CaptureIO

  @tmp "tmp/antigen_regen_task_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "regenerates seeds into the given path and prints a tally" do
    dest = Path.join(@tmp, "seeds.sexp")

    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.RegenSeeds.run(["--seeds", dest, "--count", "40"])
      end)

    assert out =~ "antigen regen_seeds:"
    assert out =~ dest
    assert File.exists?(dest)
  end
end
