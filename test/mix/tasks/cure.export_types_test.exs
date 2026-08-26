defmodule Mix.Tasks.Cure.ExportTypesTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "unknown targets render the shared usage diagnostic" do
    Mix.Task.reenable("cure.export_types")

    stderr =
      capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.export_types", ["--target", "json"])) == {:shutdown, 1}
      end)

    assert stderr =~ "INVALID COMMAND USAGE [E099]"
    assert stderr =~ "Unknown export target 'json'"
    assert stderr =~ "Supported targets: protobuf"
    refute stderr =~ "cure.export_types: unknown target"
  end

  test "invalid options render the shared usage diagnostic" do
    Mix.Task.reenable("cure.export_types")

    stderr =
      capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.export_types", ["--unknown"])) == {:shutdown, 1}
      end)

    assert stderr =~ "INVALID COMMAND USAGE [E099]"
    assert stderr =~ "Invalid options for mix cure.export_types"
    refute stderr =~ "** (MatchError)"
  end
end
