# Hardening tests for Cure.Edition — audit findings F6 (resolve/1 crashes on an
# explicit nil :source) and F8 (compare/2 crashes opaquely on a non-numeric edition).
defmodule Cure.EditionHardeningTest do
  use ExUnit.Case, async: true

  test "F6: resolve/1 tolerates an explicit nil :source and falls back to the default" do
    assert {:ok, edition} = Cure.Edition.resolve(%{source: nil, project_dir: nil})
    assert edition == Cure.Edition.current()
  end

  test "F8: compare/2 raises a clear edition-domain error on a non-numeric input" do
    assert_raise ArgumentError, ~r/edition/, fn ->
      Cure.Edition.compare("abc", "2026")
    end
  end

  test "F8: compare/2 still totally orders valid editions" do
    assert Cure.Edition.compare("2026", "2027") == :lt
    assert Cure.Edition.compare("2027", "2026") == :gt
    assert Cure.Edition.compare("2026", "2026") == :eq
  end

  # F-C (audit iteration 3): the parser tokenizes whitespace-insensitively, so
  # `@edition ("2026")` and `@ edition("2026")` are valid, compilable pragmas —
  # but the resolution pre-scan regex required a tight `@edition(`, so a spaced
  # pragma was invisible to resolution (fell through to project/default). A
  # pragma the compiler accepts must never be missed by resolution.
  test "F-C: pragma_edition tolerates the same whitespace the parser accepts" do
    assert Cure.Edition.pragma_edition("@edition (\"2026\")\nmod M\n") == "2026"
    assert Cure.Edition.pragma_edition("@ edition(\"2026\")\nmod M\n") == "2026"
    assert Cure.Edition.pragma_edition("@edition( \"2026\" )\nmod M\n") == "2026"
    assert Cure.Edition.pragma_edition("@edition(\"2026\")\nmod M\n") == "2026"
  end

  test "F-C: resolve/1 honors a whitespace-spaced pragma" do
    assert Cure.Edition.resolve(%{source: "@edition (\"2026\")\nmod M\n"}) == {:ok, "2026"}
  end

  # F1 (audit iteration 4): the parser rejects an INDENTED `@edition` (it is no
  # longer file-leading → :edition_pragma_placement), so the resolver must not
  # over-match it either. A leading-whitespace pragma is not a valid pragma; the
  # pre-scan regex is anchored at column 0 (`^@`, not `^\s*@`) so resolution and
  # the parser agree it is "no pragma" rather than silently selecting an edition
  # the parser will reject.
  test "F1: pragma_edition does not over-match an indented (non-leading) pragma" do
    assert Cure.Edition.pragma_edition("  @edition(\"2026\")\nmod M\n") == nil
    assert Cure.Edition.pragma_edition("\t@edition(\"2026\")\nmod M\n") == nil
  end
end
