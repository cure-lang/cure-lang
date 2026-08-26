defmodule Mix.Tasks.Cure.SnapTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.IO)

    path = Path.join(System.tmp_dir!(), "cure_snap_corrupt_#{System.unique_integer([:positive])}")
    File.write!(path, <<0, 1, 2, 3>>)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.snap")
      File.rm(path)
    end)

    {:ok, path: path}
  end

  test "corrupt snapshots use a structured artifact diagnostic", %{path: path} do
    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.snap")
        assert catch_exit(Mix.Task.run("cure.snap", ["load", path])) == {:shutdown, 1}
      end)

    assert output =~ "[E100]"
    assert output =~ "Snap file is corrupt or truncated"
    assert output =~ Path.basename(path)
  end
end
