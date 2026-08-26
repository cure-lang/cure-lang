defmodule Mix.Tasks.Cure.CompileTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.Process)

    dir = Path.join(System.tmp_dir!(), "cure_mix_compile_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.compile")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "directory compilation propagates a user prelude operator through the real task", %{dir: dir} do
    suffix = System.unique_integer([:positive])
    provider = "MixFixityProvider#{suffix}"
    consumer = "MixFixityConsumer#{suffix}"

    File.write!(Path.join(dir, "provider.cure"), """
    @prelude
    mod #{provider}
      precedencegroup MixFixityGroup#{suffix}
        associativity: left
      infix `<?>` : MixFixityGroup#{suffix}
      fn `<?>`(a: Int, b: Int) -> Int = a
    end
    """)

    File.write!(Path.join(dir, "consumer.cure"), """
    mod #{consumer}
      fn go() -> Int = 41 <?> 1
    end
    """)

    out = Path.join(dir, "ebin")
    Mix.Task.reenable("cure.compile")
    assert :ok = Mix.Task.run("cure.compile", [dir, "--output-dir", out])

    module = String.to_atom("Cure.#{consumer}")
    assert {:ok, published} = Cure.Compiler.Artifacts.open_verified_set(out, verification: :full)

    for authored_module <- [provider, consumer] do
      runtime_module = String.to_atom("Cure.#{authored_module}")
      assert [beam_name] = published.modules[authored_module].beams
      assert {:ok, binary} = File.read(Path.join(published.artifact_root, beam_name))
      assert {:module, ^runtime_module} = :code.load_binary(runtime_module, ~c"published", binary)
    end

    assert apply(module, :go, []) == 41
  end

  test "directory import cycles emit one structured warning on stderr", %{dir: dir} do
    suffix = System.unique_integer([:positive])
    left = "MixCycleLeft#{suffix}"
    right = "MixCycleRight#{suffix}"

    File.write!(Path.join(dir, "left.cure"), "mod #{left}\n  use #{right}\n  fn left() -> Int = 1\nend\n")
    File.write!(Path.join(dir, "right.cure"), "mod #{right}\n  use #{left}\n  fn right() -> Int = 2\nend\n")

    out = Path.join(dir, "cycle_ebin")
    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    # A cycle is a WARNING, not a failure: `load_module_interface/2` answers a
    # back-edge with an interface skeleton, so cycle members check against each
    # other's real signatures and the build completes. The stdlib relies on this
    # — `Std.Char`/`Std.Literal`/`Std.String` are mutually recursive by design.
    # What W086 buys is that the cycle is still SAID, exactly once, from the one
    # place that can see the whole file set.
    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          assert :ok = Mix.Task.run("cure.compile", [dir, "--output-dir", out])
        end)
      end)

    assert stderr =~ "IMPORT CYCLE [W086]"
    assert stderr =~ left
    assert stderr =~ right
    assert stderr =~ "Cycle members compile together in deterministic order"
    assert length(Regex.scan(~r/-- IMPORT CYCLE \[W086\]/, stderr)) == 1
    refute stderr =~ "{:import_cycle"
  end

  test "compile diagnostics render through the shared sink", %{dir: dir} do
    path = Path.join(dir, "bad.cure")
    out = Path.join(dir, "ebin")
    File.write!(path, "mod MixCompileFailure\n  fn run() -> Int = missing_name\n")
    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert :ok = Mix.Task.run("cure.compile", [path, "--output-dir", out])
      end)

    assert output =~ "[E091]"
    assert output =~ "missing_name"
    assert output =~ "^^^^^^^^^^^^"
    refute output =~ "{:unknown_global"
  end

  test "bare branch verdicts keep their branch-specific title in the Mix task", %{dir: dir} do
    path = Path.join(dir, "bad_branch.cure")
    out = Path.join(dir, "ebin_branch")

    File.write!(path, """
    mod BadBranch
      type Flag = On | Off
      fn run(flag: Flag) -> Int = match flag
        On -> 1
        Off -> true
    end
    """)

    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert :ok = Mix.Task.run("cure.compile", [path, "--output-dir", out])
      end)

    assert output =~ "PATTERN BRANCHES DISAGREE"
    assert output =~ "On -> 1"
    assert output =~ "------- compare this branch with the declared result"
    assert output =~ "Off -> true"
    assert output =~ "^^^^^^^^^^^ possible outlier: this branch has the incompatible type"
    refute output =~ "ELABORATION FAILED"
  end

  test "unknown options fail as E099 before file compilation" do
    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.compile", ["--unknown"])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Invalid options for mix cure.compile"
    refute output =~ "Compiling --unknown"
    refute output =~ "COULD NOT READ FILE"
  end

  test "missing paths use the shared E099 diagnostic" do
    Mix.shell(Mix.Shell.IO)
    Mix.Task.reenable("cure.compile")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.compile", [])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Usage: mix cure.compile <path>"
  end
end
