defmodule Mix.Tasks.Cure.Check.DocsTest do
  use ExUnit.Case, async: false

  # Every test here runs a Mix task that repoints `CURE_LIB` and the `:cure`
  # stdlib config at its own temporary project, and each `setup` is responsible
  # for handing them back. Leaking even one of them makes the *rest* of the
  # suite fail, far from here and for a reason that reads as unrelated, so this
  # guard fails the module that caused it instead.
  setup_all do
    before = env_snapshot()
    on_exit(fn -> assert env_snapshot() == before end)
    :ok
  end

  setup do
    previous_shell = Mix.shell()
    previous_cwd = File.cwd!()
    Mix.shell(Mix.Shell.IO)

    root = Path.join(System.tmp_dir!(), "cure_check_docs_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(root, "priv/doc_snippets"))
    File.write!(Path.join(root, "priv/doc_snippets/support.cure"), "")

    # The task resolves the stdlib as `_build/cure/ebin` relative to the project
    # root. Without one, artifact verification rejects every snippet with E100
    # before it is judged, and each test fails for a reason it is not testing.
    File.mkdir_p!(Path.join(root, "_build/cure"))
    compiled_stdlib = Cure.Stdlib.Paths.beam_dir() || Path.join(previous_cwd, "_build/cure/ebin")
    File.ln_s!(compiled_stdlib, Path.join(root, "_build/cure/ebin"))

    # The task points `CURE_LIB`, the `:cure` stdlib config, and the code path at
    # the project it is run in, and keeps them there -- correct for a real `mix`
    # invocation, which owns the OS process. Here the process outlives the task,
    # so all of it has to be handed back.
    #
    # Left in place, `CURE_LIB` names a temporary root that this setup then
    # deletes, and every later test resolves the standard library from a
    # directory that no longer exists; the source-JIT fallback recreates it,
    # recompiles the standard library into it, and the result collides with the
    # resident sticky set the suite loaded once at startup.
    #
    # The code path entry is worse, because it survives the deletion: the
    # snippet compiler adds `<root>/_build/cure/ebin`, and the parent of that
    # directory is literally named `cure`, so ERTS reads it as the `:cure`
    # application's lib dir. `:code.priv_dir(:cure)` then answers with the
    # temporary root, and every stdlib candidate derived from it is gone.
    previous_env = env_snapshot()

    System.cmd("git", ["init", "--quiet"], cd: root)
    File.cd!(root)

    on_exit(fn ->
      File.cd!(previous_cwd)
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.check.docs")
      restore_env(previous_env)
      File.rm_rf!(root)
    end)

    {:ok, root: root}
  end

  test "compiles every tracked Cure fence and ignores other languages", %{root: root} do
    write_and_track(root, "GUIDE.md", """
    ```cure
    fn answer() -> Int = 42
    ```

    ```elixir
    not_cure()
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  GUIDE.md:2"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "no tag opts a cure fence out of checking, but a text fence is not one", %{root: root} do
    write_and_track(root, "NOT_CODE.md", """
    ```cure pseudocode
    match xs
      [] -> 0
    ```

    ```text
    match xs
      [] -> 0
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", ["--verbose"])) == {:shutdown, 1}
        end)
      end)

    # The `cure` fence is checked despite its tag; the `text` fence below it is
    # never extracted, so exactly one snippet is judged.
    assert output =~ "FAIL NOT_CODE.md:2"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "compiles Cure fences embedded in tracked .cure docstrings", %{root: root} do
    write_and_track(root, "demo.cure", """
    mod Demo
      ## ## Examples
      ##
      ## ```cure expr
      ## 40 + 2
      ## ```
      fn answer() -> Int = 42
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  demo.cure:5"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "compiles independent expressions in one fence", %{root: root} do
    write_and_track(root, "LITERALS.md", """
    ```cure
    1 + 1
    true
    :ok
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", [])
      end)

    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "fails with the Markdown path and authored fence line", %{root: root} do
    write_and_track(root, "BROKEN.md", """
    prose

    ```cure
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert stderr =~ "UNKNOWN VALUE [E091]"
    assert stderr =~ "BROKEN.md"
    assert stderr =~ "missing"
  end

  test "rejects command arguments before scanning" do
    Mix.Task.reenable("cure.check.docs")

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.check.docs", ["unexpected"])) == {:shutdown, 1}
      end)

    assert stderr =~ "INVALID COMMAND USAGE [E099]"
    assert stderr =~ "Usage: mix cure.check.docs"
  end

  test "an error-tagged fence passes only for the expected diagnostic", %{root: root} do
    write_and_track(root, "NEGATIVE.md", """
    ```cure E091
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  NEGATIVE.md:2 (E091 as documented)"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "an error-tagged fence fails when it unexpectedly compiles", %{root: root} do
    write_and_track(root, "STALE_NEGATIVE.md", """
    ```cure E091
    fn answer() -> Int = 42
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
      end)

    assert output =~ "expected E091 but compiled"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "an error-tagged fence fails on a different diagnostic", %{root: root} do
    write_and_track(root, "WRONG_ERROR.md", """
    ```cure E003
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert output =~ "expected E003, got E091"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "a warning-tagged fence passes when the documented warning is emitted", %{root: root} do
    write_and_track(root, "WARNS.md", """
    ```cure W000
    #{deprecated_extern()}
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        Mix.Task.run("cure.check.docs", ["--verbose"])
      end)

    assert output =~ "ok  WARNS.md:2 (W000 as documented)"
    assert output =~ "doc snippets: 1 passed, 0 failed"
  end

  test "a warning-tagged fence fails when the snippet compiles cleanly", %{root: root} do
    write_and_track(root, "STALE_WARNING.md", """
    ```cure W000
    fn answer() -> Int = 42
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
      end)

    assert output =~ "expected W000 but compiled without warnings"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "a warning-tagged fence fails when the snippet does not compile", %{root: root} do
    write_and_track(root, "BROKEN_WARNING.md", """
    ```cure W000
    fn broken() -> Int = missing
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert output =~ "expected W000, got E091"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  test "an untagged fence still fails on any warning", %{root: root} do
    write_and_track(root, "UNDECLARED_WARNING.md", """
    ```cure
    #{deprecated_extern()}
    ```
    """)

    Mix.Task.reenable("cure.check.docs")

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Task.run("cure.check.docs", [])) == {:shutdown, 1}
        end)
      end)

    assert output =~ "UNDECLARED_WARNING.md:2 (1 warning(s))"
    assert output =~ "doc snippets: 0 passed, 1 failed"
  end

  # A snippet that compiles while emitting exactly one W000. `erlang:now/0` has
  # been deprecated since OTP 18, so the Erlang linter warns without any Cure
  # standard library being reachable from the temporary project root.
  defp deprecated_extern do
    """
    @extern(:erlang, :now, 0)
    fn timestamp() -> Int
    """
    |> String.trim_trailing()
  end

  defp env_snapshot do
    %{
      cure_lib: System.get_env("CURE_LIB"),
      source_dir: Application.fetch_env(:cure, :stdlib_source_dir),
      beam_dir: Application.fetch_env(:cure, :stdlib_beam_dir),
      code_path: :code.get_path()
    }
  end

  defp restore_env(previous) do
    case previous.cure_lib do
      nil -> System.delete_env("CURE_LIB")
      value -> System.put_env("CURE_LIB", value)
    end

    restore_app_env(:stdlib_source_dir, previous.source_dir)
    restore_app_env(:stdlib_beam_dir, previous.beam_dir)
    :code.set_path(previous.code_path)
  end

  defp restore_app_env(key, :error), do: Application.delete_env(:cure, key)
  defp restore_app_env(key, {:ok, value}), do: Application.put_env(:cure, key, value)

  defp write_and_track(root, relative, contents) do
    path = Path.join(root, relative)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, contents)
    System.cmd("git", ["add", "--", relative], cd: root)
  end
end
