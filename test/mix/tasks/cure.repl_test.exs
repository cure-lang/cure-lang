defmodule Mix.Tasks.Cure.ReplTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Mix.Tasks.Cure.Repl, as: Task

  describe "build_opts/1" do
    test "defaults to an empty keyword list when nothing is parsed" do
      assert [] = Task.build_opts([])
    end

    test "translates --raw and --no-raw" do
      assert [raw: true] = Task.build_opts(raw: true)
      assert [raw: false] = Task.build_opts(raw: false)
    end

    test "translates --theme names" do
      assert [theme: :dark] = Task.build_opts(theme: "dark")
      assert [theme: :light] = Task.build_opts(theme: "light")
      assert [theme: :mono] = Task.build_opts(theme: "mono")
      assert [theme: :auto] = Task.build_opts(theme: "auto")
    end

    test "translates --mode names" do
      assert [mode: :emacs] = Task.build_opts(mode: "emacs")
      assert [mode: :vi] = Task.build_opts(mode: "vi")
    end

    test "translates --history and --no-history" do
      assert [history_path: "/tmp/h"] = Task.build_opts(history: "/tmp/h")
      assert [history_path: nil] = Task.build_opts(history: "")
      assert [history_path: nil] = Task.build_opts(no_history: true)
    end

    test "translates --error-device values" do
      assert [error_device: :stdio] = Task.build_opts(error_device: "stdio")
      assert [error_device: :stderr] = Task.build_opts(error_device: "stderr")
      assert [error_device: :stdio] = Task.build_opts(error_device: "standard_io")
      assert [error_device: :stderr] = Task.build_opts(error_device: "standard_error")
    end

    test "composes multiple switches in the input order" do
      parsed = [raw: false, theme: "mono", error_device: "stdio", no_history: true]

      opts = Task.build_opts(parsed)

      assert [_, _, _, _] = opts
      assert Keyword.get(opts, :raw) == false
      assert Keyword.get(opts, :theme) == :mono
      assert Keyword.get(opts, :error_device) == :stdio
      assert Keyword.get(opts, :history_path) == nil
    end

    test "later occurrences of the same option win" do
      parsed = [theme: "dark", theme: "mono"]

      assert [theme: :mono] = Task.build_opts(parsed)
    end

    test "rejects unknown --theme values with a Mix error" do
      Mix.shell(Mix.Shell.Process)

      try do
        assert [] = Task.build_opts(theme: "neon")
        assert_received {:mix_shell, :error, [msg]}
        assert msg =~ "INVALID CONFIGURATION [W002]"
        assert msg =~ "unknown --theme"
      after
        Mix.shell(Mix.Shell.IO)
      end
    end

    test "rejects unknown --mode values with a Mix error" do
      Mix.shell(Mix.Shell.Process)

      try do
        assert [] = Task.build_opts(mode: "nano")
        assert_received {:mix_shell, :error, [msg]}
        assert msg =~ "INVALID CONFIGURATION [W002]"
        assert msg =~ "unknown --mode"
      after
        Mix.shell(Mix.Shell.IO)
      end
    end
  end

  describe "run/1 dispatch" do
    test "forwards parsed options to Cure.REPL.start/1 via the configured MFA" do
      parent = self()

      Application.put_env(:cure, :repl_start_mfa, {__MODULE__, :capture_repl_start, [parent]})

      try do
        # `mix app.start` is a no-op for already-started apps, so this
        # does not block and exercises the full dispatch path.
        capture_io(fn ->
          Task.run(["--no-raw", "--theme=mono", "--error-device=stdio", "--no-history"])
        end)

        assert_received {:repl_opts, opts}
        assert Keyword.get(opts, :raw) == false
        assert Keyword.get(opts, :theme) == :mono
        assert Keyword.get(opts, :error_device) == :stdio
        assert Keyword.get(opts, :history_path) == nil
      after
        Application.delete_env(:cure, :repl_start_mfa)
      end
    end

    test "rejects unknown switches through the shared usage diagnostic" do
      Mix.Task.reenable("cure.repl")

      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Task.run(["--unknown"])) == {:shutdown, 1}
        end)

      assert stderr =~ "INVALID COMMAND USAGE [E099]"
      assert stderr =~ "Invalid arguments for mix cure.repl"
      refute stderr =~ "** (FunctionClauseError)"
    end

    test "rejects positional arguments through the shared usage diagnostic" do
      Mix.Task.reenable("cure.repl")

      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Task.run(["unexpected"])) == {:shutdown, 1}
        end)

      assert stderr =~ "INVALID COMMAND USAGE [E099]"
      assert stderr =~ "unexpected"
    end
  end

  @doc false
  def capture_repl_start(parent, opts) do
    send(parent, {:repl_opts, opts})
    :ok
  end
end
