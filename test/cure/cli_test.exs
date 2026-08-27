defmodule Cure.CLITest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  # Most of what the CLI does it does to the working directory, and the working
  # directory belongs to the OS process, not to a test. A test that leaves it
  # somewhere it should not be breaks whatever runs next, so fail the module
  # that did it rather than the bystander.
  setup_all do
    before = File.cwd!()
    on_exit(fn -> assert File.cwd() == {:ok, before} end)
    :ok
  end

  # Run `fun` with `dir` as the working directory, restoring it afterwards.
  #
  # `File.cd!/2` restores in an `after`, which does not run when ExUnit kills a
  # timed-out test process. The directory these tests cd into is a temporary one
  # their own `on_exit` then deletes, so a single timeout leaves the whole VM
  # with no working directory at all and every later test fails on
  # `File.cwd!/0` -- far from the timeout that caused it, and looking nothing
  # like it. `on_exit` runs after the test process is gone, so registering the
  # restore there survives the kill; the `after` still restores promptly for the
  # rest of a test that completes normally.
  defp in_dir(dir, fun) do
    previous_cwd = File.cwd!()
    on_exit(fn -> File.cd!(previous_cwd) end)
    File.cd!(dir)

    try do
      fun.()
    after
      File.cd!(previous_cwd)
    end
  end

  defp ensure_escript! do
    path = Path.expand("cure")

    unless File.exists?(path) do
      Mix.Task.run("cure.escript", [])
    end

    path
  end

  describe "cure version" do
    test "prints version" do
      output = capture_io(fn -> Cure.CLI.main(["version"]) end)
      assert output =~ "Cure"
      assert output =~ Mix.Project.config()[:version]
    end
  end

  describe "cure help" do
    test "prints help text" do
      output = capture_io(fn -> Cure.CLI.main(["help"]) end)
      assert output =~ "Usage: cure"
      assert output =~ "compile"
      assert output =~ "run"
      assert output =~ "check"
      assert output =~ "lsp"
      assert output =~ "migrate [path|dir]"
      assert output =~ "--edition YYYY"
      assert output =~ "--warn-import-cycles"
    end

    test "no args shows help" do
      output = capture_io(fn -> Cure.CLI.main([]) end)
      assert output =~ "Usage: cure"
    end

    test "--help flag shows help" do
      output = capture_io(fn -> Cure.CLI.main(["--help"]) end)
      assert output =~ "Usage: cure"
    end
  end

  describe "cure compile" do
    @tag :tmp_dir
    # A genuinely cold standalone VM may need to populate the dependent
    # interface/macro cache before it can compile the first project. Keep this
    # above the observed cold-start bound; the second invocation is the
    # incremental assertion and must remain fast/no-op.
    @tag timeout: 1_200_000
    test "standalone escript compiles and incrementally reuses a regular project", %{tmp_dir: tmp} do
      project_root = Path.join(tmp, "escript_project")
      source_root = Path.join(project_root, "lib")
      output_root = Path.join(project_root, "_build/cure/project/ebin")
      File.mkdir_p!(source_root)

      File.write!(Path.join(project_root, "Cure.toml"), """
      [project]
      name = "escript_project"
      version = "0.1.0"
      edition = "2026"
      source_paths = ["lib"]
      """)

      File.write!(Path.join(source_root, "provider.cure"), """
      mod Escript.Provider
        fn answer() -> Int = 42
      """)

      File.write!(Path.join(source_root, "consumer.cure"), """
      mod Escript.Consumer
        use Escript.Provider
        fn run() -> Int = answer()
      """)

      executable = ensure_escript!()
      args = ["compile", "lib", "-o", output_root]

      assert {first_output, 0} = System.cmd(executable, args, cd: project_root, stderr_to_stdout: true)
      assert first_output =~ "Cure.Escript.Provider"
      assert first_output =~ "Cure.Escript.Consumer"

      first_pointer = File.read!(Path.join(output_root, "current"))

      assert {second_output, 0} = System.cmd(executable, args, cd: project_root, stderr_to_stdout: true)
      refute second_output =~ "Cure.Escript.Provider"
      refute second_output =~ "Cure.Escript.Consumer"
      assert File.read!(Path.join(output_root, "current")) == first_pointer
    end

    @tag :examples
    test "compiles a .cure file" do
      output =
        capture_io(fn ->
          Cure.CLI.main(["compile", "examples/hello.cure", "-o", "_build/test_cli_ebin"])
        end)

      assert output =~ "Cure.Hello"
      File.rm_rf!("_build/test_cli_ebin")
    end

    test "compiles a directory" do
      source_dir =
        Path.join(System.tmp_dir!(), "cure_cli_compile_dir_#{System.unique_integer([:positive])}")

      output_dir = Path.join(System.tmp_dir!(), "cure_cli_compile_ebin_#{System.unique_integer([:positive])}")
      File.mkdir_p!(source_dir)

      on_exit(fn ->
        File.rm_rf!(source_dir)
        File.rm_rf!(output_dir)
      end)

      File.write!(Path.join(source_dir, "first.cure"), """
      mod CureCliDirectory
        fn value() -> Int = 1
      """)

      output =
        capture_io(fn ->
          Cure.CLI.main(["compile", source_dir, "-o", output_dir])
        end)

      assert output =~ "->"
      artifact_root = Cure.Compiler.Artifacts.Writer.resolve(output_dir)
      assert File.exists?(Path.join(artifact_root, "Cure.CureCliDirectory.beam"))
    end

    @tag :tmp_dir
    @tag timeout: 1_200_000
    test "legal import-cycle diagnostics are opt-in", %{tmp_dir: tmp} do
      source_dir = Path.join(tmp, "cycle_src")
      quiet_output = Path.join(tmp, "quiet_ebin")
      warned_output = Path.join(tmp, "warned_ebin")
      File.mkdir_p!(source_dir)

      File.write!(Path.join(source_dir, "a.cure"), """
      mod CliCycle.A
        use CliCycle.B
        fn from_a() -> Int = 1
      """)

      File.write!(Path.join(source_dir, "b.cure"), """
      mod CliCycle.B
        use CliCycle.A
        fn from_b() -> Int = 2
      """)

      quiet =
        capture_io(:stderr, fn ->
          Cure.CLI.main(["compile", source_dir, "-o", quiet_output])
        end)

      refute quiet =~ "W086"

      warned =
        capture_io(:stderr, fn ->
          Cure.CLI.main(["compile", source_dir, "-o", warned_output, "--warn-import-cycles"])
        end)

      assert warned =~ "W086"
      assert warned =~ "CliCycle.A"
      assert warned =~ "CliCycle.B"
    end

    @tag :tmp_dir
    test "escript compile preloads explicit stdlib providers from a published generation", %{tmp_dir: tmp} do
      source = Path.join(tmp, "uses_result.cure")
      output_dir = Path.join(tmp, "ebin")

      File.write!(source, """
      mod UsesResult
        use Std.Result
        fn value() -> Result(Int, Atom) = Ok(42)
      """)

      assert {output, 0} =
               System.cmd(ensure_escript!(), ["compile", source, "-o", output_dir],
                 cd: tmp,
                 stderr_to_stdout: true
               )

      refute output =~ "STDLIB MODULE RESOLUTION FAILED"
      artifact_root = Cure.Compiler.Artifacts.Writer.resolve(output_dir)
      assert File.exists?(Path.join(artifact_root, "Cure.UsesResult.beam"))
    end

    @tag :tmp_dir
    @tag timeout: 600_000
    test "compiles imports from an installed path dependency", %{tmp_dir: tmp} do
      dependency = Path.join(tmp, "external_math")
      project_root = Path.join(tmp, "consumer")
      output_dir = Path.join(project_root, "_build/cure/project/ebin")
      dependency_ebin = Path.join(project_root, "_build/deps/external_math")

      File.mkdir_p!(Path.join(dependency, "lib"))
      File.mkdir_p!(Path.join(project_root, "lib"))

      File.write!(Path.join(dependency, "Cure.toml"), """
      [project]
      name = "external_math"
      version = "0.1.0"
      edition = "2026"
      """)

      File.write!(Path.join(dependency, "lib/math.cure"), """
      mod External.Math
        fn external_answer() -> Int = 42
      """)

      File.write!(Path.join(project_root, "Cure.toml"), """
      [project]
      name = "consumer"
      version = "0.1.0"
      edition = "2026"

      [dependencies]
      external_math = { path = "../external_math" }
      """)

      source = Path.join(project_root, "lib/main.cure")

      File.write!(source, """
      mod UsesExternal
        use External.Math
        fn answer() -> Int = external_answer()
      """)

      {:ok, project} = Cure.Project.load(project_root)
      assert :ok = Cure.Project.resolve_deps(project)

      on_exit(fn ->
        :code.del_path(String.to_charlist(Path.expand(dependency_ebin)))
        :code.purge(:"Cure.External.Math")
        :code.delete(:"Cure.External.Math")
        :code.purge(:"Cure.UsesExternal")
        :code.delete(:"Cure.UsesExternal")
      end)

      output =
        in_dir(project_root, fn ->
          capture_io(fn ->
            Cure.CLI.main(["compile", "lib/main.cure", "--output-dir", output_dir])
          end)
        end)

      assert output =~ "Cure.UsesExternal"
      artifact_root = Cure.Compiler.Artifacts.Writer.resolve(output_dir)
      assert File.exists?(Path.join(artifact_root, "Cure.UsesExternal.beam"))
    end

    test "no path shows a usage error and exits nonzero" do
      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["compile"])) == {:shutdown, 1}
        end)

      assert output =~ "Usage"
    end

    test "compile failures use the structured sink with source carets" do
      path = Path.join(System.tmp_dir!(), "cure_cli_diagnostic_#{System.unique_integer([:positive])}.cure")
      output_dir = Path.join(System.tmp_dir!(), "cure_cli_diagnostic_#{System.unique_integer([:positive])}")

      File.write!(path, "mod DiagnosticFailure\n  fn run() -> Int = missing_name\n")

      on_exit(fn ->
        File.rm(path)
        File.rm_rf(output_dir)
      end)

      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["compile", path, "-o", output_dir])) == {:shutdown, 1}
        end)

      assert output =~ "[E091]"
      assert output =~ "missing_name"
      assert output =~ "^^^^^^^^^^^^"
      refute output =~ "{:unknown_global"
    end

    test "mix cure.compile usage diagnostics use the shared sink" do
      output =
        ExUnit.CaptureIO.capture_io(:stderr, fn ->
          assert catch_exit(Mix.Tasks.Cure.Compile.run([])) == {:shutdown, 1}
        end)

      assert output =~ "[E099]"
      assert output =~ "INVALID COMMAND USAGE"
      refute output =~ "{:usage_error"
    end

    test "unknown options fail as E099 before compilation" do
      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["compile", "--verbsoe", "examples/hello.cure"])) ==
                   {:shutdown, 1}
        end)

      assert output =~ "INVALID COMMAND USAGE [E099]"
      assert output =~ "--verbsoe"
      refute output =~ "UNKNOWN VALUE"
      refute output =~ "Compiling examples/hello.cure"
    end
  end

  describe "cure run" do
    test "a wrong argument count is a usage error, not 'Unknown command'" do
      # `["run" | [path]]` matches exactly one arg; 0 or 2+ used to fall through
      # to the generic catch-all and get misblamed as an unknown command.
      for args <- [["run"], ["run", "a.cure", "b.cure"]] do
        output =
          capture_io(:stderr, fn ->
            assert catch_exit(Cure.CLI.main(args)) == {:shutdown, 1}
          end)

        assert output =~ "Usage: cure run"
        refute output =~ "Unknown command"
      end
    end

    test "compiles and runs a .cure file with main/0" do
      # Create a temp file with main
      path = Path.join(System.tmp_dir!(), "cure_cli_test.cure")

      File.write!(path, """
      mod CliRun
        fn main() -> Int = 42
      """)

      output = capture_io(fn -> Cure.CLI.main(["run", path]) end)
      assert output =~ "42"
    after
      :code.purge(:"Cure.CliRun")
      :code.delete(:"Cure.CliRun")
    end

    test "a missing source is an E095 file-read diagnostic" do
      path = "/no/such/cure_cli_run_missing.cure"

      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["run", path])) == {:shutdown, 1}
        end)

      assert output =~ "COULD NOT READ FILE [E095]"
      assert output =~ path
      refute output =~ "[E098]"
      refute output =~ "1 |"
    end

    test "compiles module without main" do
      path = Path.join(System.tmp_dir!(), "cure_cli_nomain.cure")

      File.write!(path, """
      mod NoMain
        fn foo() -> Int = 99
      """)

      output = capture_io(fn -> Cure.CLI.main(["run", path]) end)
      assert output =~ "no main/0"
    after
      :code.purge(:"Cure.NoMain")
      :code.delete(:"Cure.NoMain")
    end
  end

  describe "cure check" do
    @tag :examples
    test "valid file passes" do
      output =
        capture_io(fn ->
          Cure.CLI.main(["check", "examples/hello.cure"])
        end)

      assert output =~ "OK"
    end

    test "a missing source is an E095 file-read diagnostic" do
      path = "/no/such/cure_cli_check_missing.cure"

      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["check", path])) == {:shutdown, 1}
        end)

      assert output =~ "COULD NOT READ FILE [E095]"
      assert output =~ path
      refute output =~ "[E098]"
      refute output =~ "1 |"
    end

    test "validates lifted module requests before reporting OK" do
      path = Path.join(System.tmp_dir!(), "cure_cli_check_bad_lift_#{System.unique_integer([:positive])}.cure")
      File.write!(path, "lift module Elixir.Bad\n  behaviour custom_behavior\n")
      on_exit(fn -> File.rm(path) end)

      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["check", path])) == {:shutdown, 1}
        end)

      assert output =~ "LIFTED MODULE NAME IS INVALID"
      assert output =~ "Cure.Generated.Worker"
      refute output =~ "[E101]"
      refute output =~ ": OK"
    end
  end

  describe "cure stdlib" do
    # :slow — asserts CLI wiring but pays a full 126-module dependent stdlib
    # compile to do it. This is the only test of `cure stdlib`, and `cmd_stdlib`
    # shares no code with the `mix cure.compile_stdlib` task the rest of the
    # suite leans on, so it must keep running on CI. Its cold public-path build
    # legitimately exceeds ExUnit's default 60-second wall budget; retain a
    # finite test-local ceiling without weakening the rest of the suite.
    @tag :slow
    @tag timeout: 600_000
    test "compiles stdlib" do
      output_dir =
        Path.join(System.tmp_dir!(), "cure_cli_stdlib_#{System.unique_integer([:positive])}")

      on_exit(fn -> File.rm_rf!(output_dir) end)

      # The suite deliberately keeps the canonical Std modules loaded and
      # sticky. Exercise the built CLI in its own VM so this public-path test
      # cannot mistake that test-only protection for a compiler load failure.
      {output, status} =
        System.cmd(ensure_escript!(), ["stdlib", "-o", output_dir], stderr_to_stdout: true)

      assert status == 0, output
      assert output =~ "Compiling Cure standard library"
      assert output =~ "Output:"
    end
  end

  describe "unknown command" do
    test "prints error and exits nonzero" do
      # A mistyped command must not exit 0 — `cure foobar && next` should stop.
      # Mirrors the `cure deps` no-Cure.toml contract (this describe's sibling),
      # which already asserts {:shutdown, 1} on an error path.
      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["foobar"])) == {:shutdown, 1}
        end)

      assert stderr =~ "INVALID COMMAND USAGE [E099]"
      assert stderr =~ "Unknown command: foobar"
      refute stderr =~ "[E098]"
    end
  end

  describe "cure new" do
    setup do
      tmp = Path.join(System.tmp_dir!(), "cure_cli_new_test_#{System.unique_integer([:positive])}")
      File.mkdir_p!(tmp)
      previous_cwd = File.cwd!()
      File.cd!(tmp)

      on_exit(fn ->
        File.cd!(previous_cwd)
        File.rm_rf!(tmp)
      end)

      {:ok, tmp: tmp}
    end

    test "scaffolds the project tree and prints the marcli-rendered banner" do
      output = capture_io(fn -> Cure.CLI.main(["new", "acme", "--lib"]) end)

      # The banner mentions the project name, the next-step commands,
      # and the CURE_HOME guidance.
      assert output =~ "acme"
      assert output =~ "cd acme"
      assert output =~ "cure deps"
      assert output =~ "cure run lib/main.cure"
      assert output =~ "CURE_HOME"

      # And the on-disk scaffold matches what the banner advertises.
      assert File.exists?("acme/Cure.toml")
      assert File.exists?("acme/lib/main.cure")
      assert File.exists?("acme/test/main_test.cure")
    end

    test "prints a usage hint (and exits nonzero) when called without a project name" do
      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["new"])) == {:shutdown, 1}
        end)

      assert output =~ "Usage"
      assert output =~ "cure new"
    end
  end

  describe "cure explain (unknown code)" do
    test "an unknown error code fails instead of silently exiting 0" do
      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["explain", "E99999"])) == {:shutdown, 1}
        end)

      assert output =~ "Unknown error code"
    end
  end

  describe "cure fmt --aggressive (failure)" do
    test "an unparseable file makes the command fail, not report success" do
      path = Path.join(System.tmp_dir!(), "cure_fmt_bad_#{System.unique_integer([:positive])}.cure")
      # A lexically/syntactically broken source the parser rejects.
      File.write!(path, "mod M\n  fn f( -> = )(\n")
      on_exit(fn -> File.rm_rf!(path) end)

      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["fmt", "--aggressive", path])) == {:shutdown, 1}
        end)

      assert output =~ "[E094]"
      assert output =~ Path.basename(path)
      assert output =~ "^"
      assert length(Regex.scan(~r/-- .* \[E094\]/, output)) == 1
      assert output =~ "FORMATTING MAY DISCARD SOURCE DETAILS [W003]"
      assert output =~ "`cure fmt --aggressive`"
      assert output =~ "Commit or copy these files before continuing"
      assert length(Regex.scan(~r/-- .* \[W003\]/, output)) == 1
      assert :binary.match(output, "[W003]") < :binary.match(output, "[E094]")
      refute output =~ "{:expected_token"
    end
  end

  describe "cure deps" do
    setup do
      tmp = Path.join(System.tmp_dir!(), "cure_cli_deps_test_#{System.unique_integer([:positive])}")
      File.mkdir_p!(tmp)
      previous_cwd = File.cwd!()

      on_exit(fn ->
        File.cd!(previous_cwd)
        File.rm_rf!(tmp)
      end)

      {:ok, tmp: tmp, previous_cwd: previous_cwd}
    end

    test "reports the empty-deps state instead of pretending to resolve", %{tmp: tmp} do
      File.cd!(tmp)

      File.write!("Cure.toml", """
      [project]
      name = "empty_deps"
      version = "0.1.0"

      [dependencies]
      """)

      output = capture_io(fn -> Cure.CLI.main(["deps"]) end)

      assert output =~ "No dependencies declared"
      assert File.exists?("Cure.lock")
    end

    test "errors out (with non-zero exit) when there is no Cure.toml", %{tmp: tmp} do
      File.cd!(tmp)

      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["deps"])) == {:shutdown, 1}
        end)

      assert stderr =~ "COULD NOT READ FILE [E095]"
      assert stderr =~ "Cannot read `Cure.toml`"
    end

    test "an unknown deps subcommand names the bad subcommand and exits nonzero", %{tmp: tmp} do
      # `cure deps frobnicate` used to fall through to the generic catch-all,
      # which bound `unknown = "deps"` — blaming a valid command, suggesting an
      # unrelated one, and exiting 0. It must instead name the real offender
      # (`frobnicate`) and fail.
      File.cd!(tmp)

      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["deps", "frobnicate"])) == {:shutdown, 1}
        end)

      assert stderr =~ "Unknown deps subcommand: frobnicate"
      assert stderr =~ "INVALID COMMAND USAGE [E099]"
      refute stderr =~ "Unknown command: deps"
      refute stderr =~ "[E098]"
    end
  end

  describe "cure keys (malformed subcommands)" do
    # `keys` has arms for `generate <handle>` and `list` but no `[keys | rest]`
    # fallback, so any malformed invocation fell through to the generic catch-all
    # — misblaming `keys` as an unknown top-level command (and the fuzzy matcher
    # even suggested `deps`). Same defect class as the deps fix.
    for {args, label} <- [
          {["keys"], "bare"},
          {["keys", "generate"], "missing handle"},
          {["keys", "bogus"], "unknown subcommand"},
          {["keys", "list", "extra"], "extra arg"}
        ] do
      @args args
      test "an unusable keys invocation (#{label}) fails without blaming a top-level command" do
        stderr =
          capture_io(:stderr, fn ->
            assert catch_exit(Cure.CLI.main(@args)) == {:shutdown, 1}
          end)

        assert stderr =~ "keys"
        assert stderr =~ "INVALID COMMAND USAGE [E099]"
        refute stderr =~ "Unknown command: keys"
        refute stderr =~ "[E098]"
      end
    end
  end

  describe "positional command usage diagnostics" do
    for command <- ~w(replay draw) do
      @command command

      test "cure #{command} without a path is E099" do
        stderr =
          capture_io(:stderr, fn ->
            assert catch_exit(Cure.CLI.main([@command])) == {:shutdown, 1}
          end)

        assert stderr =~ "INVALID COMMAND USAGE [E099]"
        assert stderr =~ "Usage: cure #{@command}"
        refute stderr =~ "[E098]"
      end
    end
  end

  describe "missing-file handling for fmt / doc" do
    # `cure fmt typo.cure` is an everyday mistake. fmt/doc read each target with
    # File.read!, which raised an uncaught File.Error (BEAM stacktrace) on a
    # missing file — unlike run/check/compile, which report + exit 1. A missing
    # explicit target must be a clean non-zero exit, never a crash.
    test "cure fmt on a missing file exits 1 without crashing" do
      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["fmt", "/no/such/missing_fmt_xyz.cure"])) ==
                   {:shutdown, 1}
        end)

      assert output =~ "COULD NOT READ FILE [E095]"
      assert output =~ "/no/such/missing_fmt_xyz.cure"
      refute output =~ "[E098]"
      refute output =~ "1 |"
    end

    test "cure fmt --check on a missing file exits 1 without crashing" do
      capture_io(:stderr, fn ->
        assert catch_exit(Cure.CLI.main(["fmt", "--check", "/no/such/missing_fmtc_xyz.cure"])) ==
                 {:shutdown, 1}
      end)
    end

    test "cure doc on a missing file exits 1 without crashing" do
      output =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["doc", "/no/such/missing_doc_xyz.cure"])) ==
                   {:shutdown, 1}
        end)

      assert output =~ "COULD NOT READ FILE [E095]"
      assert output =~ "/no/such/missing_doc_xyz.cure"
      refute output =~ "[E098]"
      refute output =~ "1 |"
    end

    # `File.exists?` returns true for a file that exists but is unreadable
    # (chmod 000), so the missing-file guard let it through to a worker whose
    # `File.read!` then raised a raw File.Error stacktrace. A permission error
    # must degrade to a clean exit 1, exactly as run/check (which read with
    # File.read) already do.
    for {cmd, label} <- [{"fmt", "fmt"}, {"fmt --check", "fmt --check"}, {"doc", "doc"}] do
      @cmd_args String.split(cmd)
      test "cure #{label} on an unreadable (existing) file exits 1 without crashing" do
        path =
          Path.join(
            System.tmp_dir!(),
            "cure_noperm_#{System.unique_integer([:positive])}.cure"
          )

        File.write!(path, "mod M\n  fn f() -> Int = 1\n")
        File.chmod!(path, 0o000)

        on_exit(fn ->
          File.chmod(path, 0o644)
          File.rm_rf!(path)
        end)

        # Root (and some CI) can read a 0o000 file; only meaningful when the
        # permission bits actually deny this process a read.
        if match?({:error, _}, File.read(path)) do
          capture_io(:stderr, fn ->
            assert catch_exit(Cure.CLI.main(@cmd_args ++ [path])) == {:shutdown, 1}
          end)
        end
      end
    end
  end

  describe "fixed-arity commands reject extra args (not misblamed as unknown)" do
    # These commands take zero positional args. An extra positional one matched
    # neither the exact `["cmd"]` arm nor any other, so it fell through to the
    # generic catch-all — which bound `unknown = "<cmd>"` and printed
    # "Unknown command: <cmd>", blaming a VALID command (and the fuzzy matcher
    # even suggested an unrelated one). Same defect class as the run/check/deps/keys
    # fixes: name the misuse and fail, never misblame. The fallback also means the
    # extra arg is rejected BEFORE the command runs, so a stray arg can't start the
    # lsp server / repl / a stdlib compile.
    for cmd <- ~w(lsp stdlib version test repl doctor fix john) do
      @cmd cmd
      test "cure #{cmd} with an extra positional arg is a usage error" do
        stderr =
          capture_io(:stderr, fn ->
            assert catch_exit(Cure.CLI.main([@cmd, "bogus_extra"])) == {:shutdown, 1}
          end)

        assert stderr =~ "Usage: cure #{@cmd}"
        refute stderr =~ "Unknown command"
      end
    end
  end

  describe "cure help with extra args" do
    test "shows help instead of misblaming 'help' as an unknown command" do
      # `["help"]` was an exact arm with no `| _` fallback, so `cure help extra`
      # fell through to the generic catch-all and printed "Unknown command: help"
      # — blaming the help command itself. Extra args to `help` should just show
      # help (standard CLI behavior), never misblame.
      output = capture_io(fn -> Cure.CLI.main(["help", "bogus"]) end)
      assert output =~ "Usage: cure"
      refute output =~ "Unknown command"
    end
  end

  describe "cure test" do
    test "does not compile intentionally invalid oracle and fixture sources" do
      root = Path.join(System.tmp_dir!(), "cure_cli_negative_corpus_#{System.unique_integer([:positive])}")
      File.mkdir_p!(Path.join(root, "test/oracle"))
      File.mkdir_p!(Path.join(root, "test/fixtures"))

      invalid = "mod Negative\n  fn broken() -> Int = missing_name\n"
      File.write!(Path.join(root, "test/oracle/broken.cure"), invalid)
      File.write!(Path.join(root, "test/fixtures/broken.cure"), invalid)
      on_exit(fn -> File.rm_rf!(root) end)

      output =
        capture_io(fn ->
          in_dir(root, fn -> Cure.CLI.main(["test"]) end)
        end)

      assert output =~ "No runnable test files found"
      assert output =~ "0 passed, 0 failed"
      refute output =~ "UNKNOWN VALUE [E091]"
    end

    test "runtime failures use an operational diagnostic" do
      root = Path.join(System.tmp_dir!(), "cure_cli_test_#{System.unique_integer([:positive])}")
      test_dir = Path.join(root, "test")
      File.mkdir_p!(test_dir)

      File.write!(Path.join(test_dir, "failure.cure"), """
      mod FailingCureTest
        @extern(:erlang, :error, 1)
        local fn explode(reason: Atom) -> Unit
        fn test_failure() -> Unit = explode(:boom)
      end
      """)

      on_exit(fn -> File.rm_rf!(root) end)

      stderr =
        capture_io(:stderr, fn ->
          in_dir(root, fn ->
            assert catch_exit(Cure.CLI.main(["test"])) == {:shutdown, 1}
          end)
        end)

      assert stderr =~ "[E098]"
      assert length(Regex.scan(~r/-- COMMAND FAILED \[E098\]/, stderr)) == 1
      refute stderr =~ "FAIL test/failure.cure"
      refute stderr =~ "{:"
    end

    test "doctest compile failures keep their compiler category and source caret" do
      root = Path.join(System.tmp_dir!(), "cure_cli_doctest_#{System.unique_integer([:positive])}")
      File.mkdir_p!(Path.join(root, "lib"))
      File.mkdir_p!(Path.join(root, "test"))

      File.write!(Path.join(root, "lib/demo.cure"), """
      mod Demo
        ## Example.
        ##
        ##   cure> missing_name
        ##   => 0
        fn example() -> Int = 0
      end
      """)

      File.write!(Path.join(root, "test/empty.cure"), "mod EmptyTests\nend\n")
      on_exit(fn -> File.rm_rf!(root) end)

      stderr =
        capture_io(:stderr, fn ->
          in_dir(root, fn ->
            assert catch_exit(Cure.CLI.main(["test", "--doctests"])) == {:shutdown, 1}
          end)
        end)

      assert stderr =~ "UNKNOWN VALUE [E091]"
      assert stderr =~ "fn main() = missing_name"
      assert stderr =~ "^^^^^^^^^^^^"
      refute stderr =~ "COMMAND FAILED [E098]"
      refute stderr =~ "compile error:"
      refute stderr =~ "{:unknown_global"
    end
  end

  describe "unknown-command suggestions" do
    # `migrate` is a real dispatch command (cli.ex) but was absent from the
    # known_commands list the "did you mean" suggester searches, so a near-miss
    # typo never proposed it.
    test "a typo near 'migrate' suggests migrate" do
      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["migrat"])) == {:shutdown, 1}
        end)

      assert stderr =~ "migrate"
    end
  end

  describe "cure audit trust" do
    test "a malformed audit invocation prints usage and exits non-zero" do
      # Round 3 found these fell through to a wrong 'Unknown command: audit'
      # with exit 0. Each must print usage and exit {:shutdown, 1}.
      for argv <- [["audit"], ["audit", "trust"], ["audit", "bogus", "X"], ["audit", "trust", "A", "B"]] do
        stderr =
          capture_io(:stderr, fn ->
            assert catch_exit(Cure.CLI.main(argv)) == {:shutdown, 1}, "argv=#{inspect(argv)}"
          end)

        assert stderr =~ "Usage: cure audit trust", "argv=#{inspect(argv)}"
      end
    end

    test "an unknown module exits non-zero" do
      stderr =
        capture_io(:stderr, fn ->
          assert catch_exit(Cure.CLI.main(["audit", "trust", "Std.NoSuchModule"])) ==
                   {:shutdown, 1}
        end)

      assert stderr =~ "no such module"
    end

    test "--strict on clean stdlib modules exits normally" do
      io = capture_io(fn -> Cure.CLI.main(["audit", "trust", "Std.Io", "--strict"]) end)
      assert io =~ "UNAUDITED (0)"

      out = capture_io(fn -> Cure.CLI.main(["audit", "trust", "Std.List", "--strict"]) end)
      assert out =~ "AXIOMS — OTP (1)"
    end
  end
end
