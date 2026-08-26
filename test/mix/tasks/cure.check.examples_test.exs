defmodule Mix.Tasks.Cure.Check.ExamplesTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    previous_cwd = File.cwd!()
    compiled_stdlib = Cure.Stdlib.Paths.beam_dir() || Path.join(previous_cwd, "_build/cure/ebin")
    Mix.shell(Mix.Shell.IO)

    dir = Path.join(System.tmp_dir!(), "cure_check_examples_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(dir, "examples"))
    File.mkdir_p!(Path.join(dir, "_build/cure"))
    File.ln_s!(compiled_stdlib, Path.join(dir, "_build/cure/ebin"))
    File.cd!(dir)

    on_exit(fn ->
      File.cd!(previous_cwd)
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.check.examples")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "compile failures are standalone diagnostics with authored source carets", %{dir: dir} do
    File.write!(
      Path.join(dir, "examples/broken.cure"),
      "mod BrokenExample\n  fn run() -> Int = missing_value\nend\n"
    )

    Mix.Task.reenable("cure.check.examples")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          assert catch_exit(Mix.Task.run("cure.check.examples", [])) == {:shutdown, 1}
        end)
      end)

    assert stderr =~ "UNKNOWN VALUE [E091]"
    assert stderr =~ "fn run() -> Int = missing_value"
    assert stderr =~ "^^^^^^^^^^^^^"
    refute stderr =~ "FAIL broken"
    refute stderr =~ "{:unknown_global"
  end

  test "wrong example output is a structured operational failure", %{dir: dir} do
    File.write!(
      Path.join(dir, "examples/hello.cure"),
      "mod Hello\n  fn main() -> Int = 41\nend\n"
    )

    Mix.Task.reenable("cure.check.examples")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          assert catch_exit(Mix.Task.run("cure.check.examples", [])) == {:shutdown, 1}
        end)
      end)

    assert stderr =~ "COMMAND FAILED [E098]"
    assert stderr =~ "example hello failed: expected 42, got 41"
    refute stderr =~ "1 |"
  end

  test "arguments fail through the shared E099 diagnostic before checking examples" do
    Mix.Task.reenable("cure.check.examples")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.check.examples", ["unexpected"])) == {:shutdown, 1}
      end)

    assert stderr =~ "INVALID COMMAND USAGE [E099]"
    assert stderr =~ "Usage: mix cure.check.examples"
  end
end
