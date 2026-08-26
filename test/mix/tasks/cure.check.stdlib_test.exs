defmodule Mix.Tasks.Cure.Check.StdlibTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    previous_cwd = File.cwd!()
    Mix.shell(Mix.Shell.IO)

    dir = Path.join(System.tmp_dir!(), "cure_check_stdlib_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(dir, "lib/std"))
    File.cd!(dir)

    on_exit(fn ->
      File.cd!(previous_cwd)
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.check.stdlib")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "compiler failures are standalone diagnostics with source carets", %{dir: dir} do
    path = Path.join(dir, "lib/std/broken.cure")
    File.write!(path, "mod Broken\n  fn run() -> Int = missing_value\nend\n")
    Mix.Task.reenable("cure.check.stdlib")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          assert catch_exit(Mix.Task.run("cure.check.stdlib", [])) == {:shutdown, 1}
        end)
      end)

    assert stderr =~ "UNKNOWN VALUE [E091]"
    assert stderr =~ "fn run() -> Int = missing_value"
    assert stderr =~ "^^^^^^^^^^^^^"
    refute stderr =~ "FAIL broken"
    refute stderr =~ "{:unknown_global"
  end

  test "arguments fail through the shared E099 diagnostic before compilation" do
    Mix.Task.reenable("cure.check.stdlib")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.check.stdlib", ["unexpected"])) == {:shutdown, 1}
      end)

    assert stderr =~ "INVALID COMMAND USAGE [E099]"
    assert stderr =~ "Usage: mix cure.check.stdlib"
  end
end
