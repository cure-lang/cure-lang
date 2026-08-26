defmodule Mix.Tasks.Cure.ReplayTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.IO)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.replay")
    end)

    :ok
  end

  test "missing paths use the shared E099 diagnostic" do
    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.replay")
        assert catch_exit(Mix.Task.run("cure.replay", [])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Usage: mix cure.replay"
  end

  test "unknown options fail before loading a journal" do
    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.replay")
        assert catch_exit(Mix.Task.run("cure.replay", ["--unknown", "missing.journal"])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    refute output =~ "COULD NOT READ FILE"
  end

  test "missing journals use one unwrapped E095 diagnostic" do
    path = Path.join(System.tmp_dir!(), "missing_replay_#{System.unique_integer([:positive])}.journal")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        Mix.Task.reenable("cure.replay")
        assert catch_exit(Mix.Task.run("cure.replay", [path])) == {:shutdown, 1}
      end)

    assert output =~ "COULD NOT READ FILE [E095]"
    assert output =~ path
    assert length(Regex.scan(~r/-- COULD NOT READ FILE \[E095\]/, output)) == 1
    refute output =~ "{:file_read_error"
    refute output =~ "1 |"
  end
end
