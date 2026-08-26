defmodule Cure.CLI.MigrateCliTest do
  use ExUnit.Case, async: false
  alias Cure.Migrate
  alias Cure.CLI

  setup do
    dir = Path.join(System.tmp_dir!(), "curemig_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    {_, 0} = System.cmd("git", ["init", "-q", dir])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.email", "t@t"])
    {_, 0} = System.cmd("git", ["-C", dir, "config", "user.name", "t"])
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "untracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    assert {:error, [{^f, :untracked}]} = Migrate.git_guard([f])
  end

  test "dirty (uncommitted) tracked file is rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# changed\n")
    assert {:error, [{^f, :dirty}]} = Migrate.git_guard([f])
  end

  test "staged-only change (index dirty, no worktree diff) is still rejected", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    File.write!(f, "mod A\n# staged\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    assert {:error, [{^f, :dirty}]} = Migrate.git_guard([f])
  end

  test "clean tracked file passes", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    assert :ok = Migrate.git_guard([f])
  end

  test "a mixed batch reports each file's own reason, not one reason for all", %{dir: dir} do
    # Proves the per-file list shape: one file is untracked, a second is a
    # dirty tracked file, a third is clean -- a single {reason, [path]} pair
    # could not represent "untracked" and "dirty" simultaneously without
    # misreporting one of them.
    untracked_f = Path.join(dir, "untracked.cure")
    dirty_f = Path.join(dir, "dirty.cure")
    clean_f = Path.join(dir, "clean.cure")

    File.write!(dirty_f, "mod D\n")
    File.write!(clean_f, "mod C\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "dirty.cure", "clean.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    File.write!(untracked_f, "mod U\n")
    File.write!(dirty_f, "mod D\n# changed\n")

    assert {:error, reasons} = Migrate.git_guard([untracked_f, dirty_f, clean_f])
    assert {untracked_f, :untracked} in reasons
    assert {dirty_f, :dirty} in reasons
    refute Enum.any?(reasons, &match?({^clean_f, _}, &1))
  end

  test "in-place migrate rewrites a clean tracked file and reparses", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    assert :ok = CLI.cmd_migrate([f], [])

    out = File.read!(f)
    assert out =~ "pickup"
  end

  test "a dirty tree is rejected with the per-file git-guard detail, not a single flattened reason",
       %{dir: dir} do
    # Proves cmd_migrate/2 propagates git_guard/1's per-file [{path, reason}]
    # list under one :git_guard_failed tag end-to-end, rather than re-flattening
    # it back into a single top-level reason atom (which would reintroduce the
    # mixed-batch ambiguity Task 11 fixed at the Cure.Migrate.git_guard/1 layer).
    clean_f = Path.join(dir, "clean.cure")
    File.write!(clean_f, "mod C\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "clean.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    untracked_f = Path.join(dir, "untracked.cure")
    File.write!(untracked_f, "mod U\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")

    before_clean = File.read!(clean_f)
    before_untracked = File.read!(untracked_f)

    parent = self()

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        send(parent, {:migration_result, CLI.cmd_migrate([clean_f, untracked_f], [])})
      end)

    assert_receive {:migration_result, {:error, {:git_guard_failed, reasons}}}
    assert {untracked_f, :untracked} in reasons
    assert stderr =~ "COMMAND FAILED [E098]"
    assert flowed(stderr) =~ "because it is not tracked by git"
    assert stderr =~ untracked_f
    refute stderr =~ "{:git_guard_failed"
    refute Enum.any?(reasons, &match?({^clean_f, _}, &1))
    # nothing was written -- the git guard runs before the batch preflight
    assert File.read!(clean_f) == before_clean
    assert File.read!(untracked_f) == before_untracked
  end

  test "batch atomicity: if one file fails, zero files are written", %{dir: dir} do
    good = Path.join(dir, "good.cure")
    bad = Path.join(dir, "bad.cure")
    File.write!(good, "mod G\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    # NB: Cure's parser is lenient enough that the plan's original
    # "this is not valid cure @@@" fixture actually parses (as an expression
    # sequence). This unterminated param list genuinely fails to parse
    # (`expected :rparen, got :eof`), which is what exercises the preflight
    # failure path. Verified 2026-07-10.
    File.write!(bad, "mod B\nfn f( = \n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "."])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    before_good = File.read!(good)
    parent = self()

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        send(parent, {:migration_result, CLI.cmd_migrate([good, bad], [])})
      end)

    assert_receive {:migration_result, {:error, {:preflight_failed, failed}}}
    assert bad in failed
    assert stderr =~ "COMMAND FAILED [E098]"
    assert flowed(stderr) =~ "producing invalid syntax or changing its comments"
    assert stderr =~ bad
    # good is untouched because bad failed the in-memory preflight
    assert File.read!(good) == before_good
  end

  test "--check prints a git-style diff, writes nothing, and reports pending", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert {:error, {:pending, [^f]}} = CLI.cmd_migrate([f], check: true)
      end)

    assert output =~ "--- a/a.cure"
    assert output =~ "+++ b/a.cure"
    assert output =~ "-fn f(x: Int) -> Int = if x > 0 then 1 else 2"
    assert output =~ "+fn f(x: Int) -> Int = pickup"
    assert output =~ "+  x > 0 -> 1"
    # --check never writes, regardless of outcome
    assert File.read!(f) == before
  end

  test "--check on an already-canonical file returns :ok and writes nothing", %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = x\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    assert :ok = CLI.cmd_migrate([f], check: true)
    assert File.read!(f) == before
  end

  test "--check resolves imported nominal types using the source path", %{dir: dir} do
    f = Path.join(dir, "a.cure")

    File.write!(f, """
    mod A
      use Std.ExitReason
      fn keep(reason: ExitReason) -> ExitReason = reason
    """)

    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    assert :ok = CLI.cmd_migrate([f], check: true)
    assert File.read!(f) == before
  end

  test "--print emits the migrated form to stdout and writes nothing, even on a dirty (unguarded) tree",
       %{dir: dir} do
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    # deliberately NOT added/committed: --print is read-only and git-guard-exempt
    before = File.read!(f)

    output =
      ExUnit.CaptureIO.capture_io(fn ->
        assert :ok = CLI.cmd_migrate([f], print: true)
      end)

    assert output =~ "pickup"
    assert File.read!(f) == before
  end

  test "--strict promotes a fixable-tier migration warning to an error and writes nothing",
       %{dir: dir} do
    # Spec §8 (Task 11): --strict now promotes only FIXABLE-tier
    # (:machine/:review) warnings, replacing the old "any warning blocks"
    # contract. The `if/then/else` here fires the :machine `:W_if_elif_pickup`
    # rule, so it is promoted to a {:strict_violation, _} error.
    f = Path.join(dir, "a.cure")
    File.write!(f, "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "a.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    parent = self()

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        send(parent, {:migration_result, CLI.cmd_migrate([f], strict: true)})
      end)

    assert_receive {:migration_result, {:error, {:strict_violation, violators}}}
    assert Enum.any?(violators, fn {p, ids} -> p == f and :W_if_elif_pickup in ids end)
    assert flowed(stderr) =~ "rejected by `--strict`"
    assert stderr =~ "W_if_elif_pickup"
    assert File.read!(f) == before
  end

  test "--strict does NOT promote a :manual warning — it stays a block, not a strict error",
       %{dir: dir} do
    # Spec §8: a lone :manual warning (a removed-module reference) is never
    # promoted by --strict. It is reported through the ordinary :blocked path
    # (phase-2 refusal), never as {:strict_violation, _}.
    f = Path.join(dir, "m.cure")
    File.write!(f, "mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n")
    {_, 0} = System.cmd("git", ["-C", dir, "add", "m.cure"])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])
    before = File.read!(f)

    parent = self()

    stderr =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        send(parent, {:migration_result, CLI.cmd_migrate([f], strict: true)})
      end)

    assert_receive {:migration_result, {:error, {:blocked, blocked}}}
    assert Enum.any?(blocked, fn {p, ids} -> p == f and :W_removed_module in ids end)
    assert flowed(stderr) =~ "manual migration for"
    assert stderr =~ "W_removed_module"
    refute match?({:error, {:strict_violation, _}}, CLI.cmd_migrate([f], strict: true))
    assert File.read!(f) == before
  end

  test "no explicit paths: scans lib/**/*.cure and test/**/*.cure under cwd, mirroring cmd_fmt/2, and nothing else",
       %{dir: dir} do
    # Spec §5.6 explicitly requires this default-scan behavior, distinct from
    # every other test in this file (which all pass an explicit path) -- this
    # is the one test exercising it. Sandboxed via File.cd!/2 (which restores
    # cwd on return, even if the callback raises) so a bug here can never
    # touch this project's own `.cure` files.
    lib_dir = Path.join(dir, "lib")
    test_dir = Path.join(dir, "test")
    other_dir = Path.join(dir, "other")
    Enum.each([lib_dir, test_dir, other_dir], &File.mkdir_p!/1)

    in_lib = Path.join(lib_dir, "a.cure")
    in_test = Path.join(test_dir, "a_test.cure")
    outside_scan = Path.join(other_dir, "z.cure")

    body = "mod A\nfn f(x: Int) -> Int = if x > 0 then 1 else 2\n"
    File.write!(in_lib, body)
    File.write!(in_test, body)
    File.write!(outside_scan, body)

    {_, 0} = System.cmd("git", ["-C", dir, "add", "."])
    {_, 0} = System.cmd("git", ["-C", dir, "commit", "-qm", "x"])

    File.cd!(dir, fn ->
      assert :ok = CLI.cmd_migrate([], [])
    end)

    assert File.read!(in_lib) =~ "pickup"
    assert File.read!(in_test) =~ "pickup"
    # a .cure file outside lib/**/test/** must not be touched by the default
    # (no-explicit-paths) scan, same as cmd_fmt/2's own file-discovery.
    refute File.read!(outside_scan) =~ "pickup"
  end

  # Collapse the runs of whitespace a rendered diagnostic contains so a phrase
  # assertion tests the MESSAGE, not where it happened to wrap.
  #
  # `Cure.Diagnostic.Doc` hard-wraps prose at the sink's 80 columns, and these
  # fixtures live under a temp dir named with `System.unique_integer/1` — whose
  # width grows as the suite runs. The interpolated path therefore shifts every
  # following word, so a phrase like "...not tracked by git" breaks across a
  # line boundary at a position that depends on how many tests ran first: the
  # same assertion passes in isolation and fails inside the full suite.
  defp flowed(text), do: String.replace(text, ~r/\s+/u, " ")
end
