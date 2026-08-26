# Hardening tests for the migrate CLI — audit findings F9 (bump pragma regex
# looser than Edition → crash) and F4 (downgrade guard must measure against the
# project edition). F4/F5's end-to-end downgrade path is unreachable with a single
# minted edition (the --edition flag is allow-list-validated first, and
# Project.load rejects an unknown edition), so this covers the reachable units.
defmodule Cure.CLI.MigrateEditionHardeningTest do
  use ExUnit.Case, async: true

  test "F9: migrate_edition_pragma accepts a 4-digit year and rejects malformed values" do
    assert Cure.CLI.migrate_edition_pragma("@edition(\"2026\")\nmod M\n") == "2026"
    assert Cure.CLI.migrate_edition_pragma("@edition(\"abc\")\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("@edition(2026)\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("@edition(\"20260\")\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("mod M\n") == nil
  end

  # F-C (audit iteration 3): the phase-2 bump detector must recognise the same
  # spaced pragmas the parser accepts, or a bump would splice a SECOND pragma
  # above an existing (spaced) one. Mirror the parser's whitespace tolerance.
  test "F-C: migrate_edition_pragma tolerates whitespace the parser accepts" do
    assert Cure.CLI.migrate_edition_pragma("@edition (\"2026\")\nmod M\n") == "2026"
    assert Cure.CLI.migrate_edition_pragma("@ edition(\"2026\")\nmod M\n") == "2026"
    assert Cure.CLI.migrate_edition_pragma("@edition( \"2026\" )\nmod M\n") == "2026"
  end

  # Finding 1 (audit iteration 4, TODAY-triggerable regression): the phase-2 bump
  # detector and splicer must only recognise a FILE-LEADING pragma (the first
  # substantive line), never an `@edition(...)` buried in a comment or string.
  # The F-C whitespace widening had extended a latent whole-body scan so a spaced
  # `@ edition("2020")` inside a comment falsely matched → a false "bumped" report
  # plus in-comment mutation while never adding a real leading pragma. Detection
  # must agree with Cure.Edition.pragma_edition (anchored to the first line).
  test "Finding 1: an @edition inside a comment is not a leading pragma (no false bump)" do
    assert Cure.CLI.migrate_edition_pragma("# migrate with @ edition (\"2020\")\nmod M\n") == nil
    assert Cure.CLI.migrate_edition_pragma("# see @edition(\"2020\")\nmod M\n") == nil
  end

  test "Finding 1: splicing prepends a real pragma and leaves an in-comment mention intact" do
    body = "# migrate with @ edition (\"2020\")\nmod M\n"
    out = Cure.CLI.migrate_splice_edition(body, "2026")
    assert out == "@edition(\"2026\")\n" <> body
    assert out =~ "# migrate with @ edition (\"2020\")"
  end

  test "Finding 1: splicing replaces an existing leading pragma after leading comments" do
    body = "# header\n@edition(\"2020\")\nmod M\n"
    out = Cure.CLI.migrate_splice_edition(body, "2026")
    assert out == "# header\n@edition(\"2026\")\nmod M\n"
  end

  # Iter-4 audit (LOW regression): the old substring Regex.replace preserved a
  # file's CRLF line endings; the rewritten line-oriented splice must too, or the
  # replaced pragma line drops its \r and the file ends up with mixed EOL.
  test "Finding 1: splicing preserves CRLF line endings on the replaced pragma line" do
    body = "@edition(\"2020\")\r\nmod M\r\n"
    out = Cure.CLI.migrate_splice_edition(body, "2026")
    assert out == "@edition(\"2026\")\r\nmod M\r\n"
  end

  # Finding (audit iteration 6): the splicer's line-finder (migrate_trivia_line?)
  # only skipped blank/`#`-comment lines, so it was blind to `###`-fenced doc
  # comments whose BODY lines need not start with `#`. It therefore diverged from
  # Cure.Edition.pragma_edition's fence-aware scan: on a file whose real leading
  # pragma sits after a fenced doc comment, the finder stopped INSIDE the fence
  # and rewrote the wrong line. (Reachable once a second edition exists, i.e. when
  # a bump actually rewrites a pragma; exercised here via migrate_splice_edition.)
  test "Finding: splice skips a fenced doc comment and bumps the real pragma, not the fence body" do
    body = "###\ndoc line\n###\n@edition(\"2026\")\nfn f() -> Int = 1\n"
    out = Cure.CLI.migrate_splice_edition(body, "2099")
    # The real pragma is bumped; the fence and its body line are untouched.
    assert out == "###\ndoc line\n###\n@edition(\"2099\")\nfn f() -> Int = 1\n"
  end

  test "Finding: splice leaves an @edition example inside a fenced doc comment alone" do
    body = "###\n@edition(\"1900\")\n###\n@edition(\"2026\")\nfn f() -> Int = 1\n"
    out = Cure.CLI.migrate_splice_edition(body, "2099")
    # Only the real leading pragma moves; the in-fence example stays 1900.
    assert out == "###\n@edition(\"1900\")\n###\n@edition(\"2099\")\nfn f() -> Int = 1\n"
  end

  test "F4: migrate_project_edition falls back to current() when no project is present" do
    dir = Path.join(System.tmp_dir!(), "cure_noproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    assert Cure.CLI.migrate_project_edition(dir) == {:ok, Cure.Edition.current()}
  end

  test "F4: migrate_project_edition reads a declared [project].edition" do
    dir = Path.join(System.tmp_dir!(), "cure_proj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    # Uses the one minted edition; confirms the helper resolves the project value
    # (not a crash / not something else) even though it equals current() today.
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    assert Cure.CLI.migrate_project_edition(dir) == {:ok, "2026"}
  end

  # I4 (audit iteration 2): a Cure.toml declaring an edition the compiler does
  # not know must be SURFACED, not masked as current() — masking would let a
  # broken project edition wave through a real downgrade. "1999" is guaranteed
  # off the known-editions allow-list.
  test "I4: migrate_project_edition surfaces an unknown declared edition" do
    dir = Path.join(System.tmp_dir!(), "cure_badproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"1999\"\n")
    assert Cure.CLI.migrate_project_edition(dir) == {:error, {:unknown_edition, "1999"}}
  end

  # The pure downgrade comparison honours the passed :current (this is what the
  # F4 wiring feeds the project edition into). compare/2 is allow-list-independent,
  # so a hypothetical older/newer edition is a valid probe.
  test "F4/F5: plan_migration refuses a target older than :current and accepts otherwise" do
    assert {:error, :downgrade} = Cure.CLI.plan_migration(target: "2026", current: "2027")
    assert {:ok, "2027"} = Cure.CLI.plan_migration(target: "2027", current: "2026")
    assert {:ok, "2026"} = Cure.CLI.plan_migration(target: "2026", current: "2026")
  end

  # Finding 2 (audit iteration 4, LATENT): the project-level downgrade guard
  # (plan_migration/1) measures the TARGET against the PROJECT edition, but a
  # single file can pin a newer edition via its own @edition pragma — `from`. If
  # `from` is newer than `target`, migrating that file is a per-file downgrade
  # and must be refused, exactly as plan_migration refuses a project downgrade.
  # Unreachable today (a future pragma is rejected as unknown before this point),
  # so probed at the pure-planner unit with a pragma-less source and hypothetical
  # editions (compare/2 is allow-list-independent, and no pragma means the parser
  # never validates a year against the allow-list).
  test "Finding 2: plan_migration_source refuses a file whose :from is newer than :target" do
    src = "mod M\n  fn f() -> Int = 1\n"
    assert {:error, :downgrade} = Cure.CLI.plan_migration_source(src, target: "2026", from: "2027")
  end

  test "Finding 2: plan_migration_source still migrates when :from is at or below :target" do
    src = "mod M\n  fn f() -> Int = 1\n"

    assert {:ok, _printed, _warns, "2026"} =
             Cure.CLI.plan_migration_source(src, target: "2026", from: "2026")
  end

  # Iteration 6 (audit A3-F2): the splice replaces the LEADING PRAGMA TOKEN, not
  # the whole line. `pragma_capture`'s regex is deliberately unanchored at the end
  # (so resolution still reads `@edition("2026")  # note` — the parser treats the
  # trailing comment as trivia), which means a whole-LINE replacement would delete
  # any trailing content. Preserve everything after the `)`.
  test "A3-F2: splicing preserves a trailing comment on the pragma line" do
    spliced = Cure.CLI.migrate_splice_edition("@edition(\"2026\")  # pin the surface\nmod M\n", "2026")

    assert String.contains?(spliced, "# pin the surface"),
           "trailing comment on the pragma line must survive the bump, got: #{inspect(spliced)}"

    assert String.starts_with?(spliced, "@edition(\"2026\")")
    assert String.contains?(spliced, "mod M")
  end

  # Iteration 6 (audit A3-F1): a lone-CR (`\r`-terminated) file has no `\n`, so
  # splitting on "\n" yields ONE element = the whole file. Replacing that element
  # wholesale would destroy the body. Replacing only the matched pragma prefix
  # keeps the rest of the file intact.
  test "A3-F1: splicing a lone-CR file does not destroy the body" do
    body = "@edition(\"2026\")\rmod M\r  fn f() -> Int = 1\r"
    spliced = Cure.CLI.migrate_splice_edition(body, "2026")

    assert String.contains?(spliced, "mod M"),
           "lone-CR body must survive the bump, got: #{inspect(spliced)}"

    assert String.contains?(spliced, "fn f()")
    assert String.starts_with?(spliced, "@edition(\"2026\")")
  end
end
