# Hardening tests for Cure.Project.set_edition/2 — audit finding F10: a [project]
# header with a trailing comment caused a duplicate table, and the existing-key
# replacement rewrote `edition =` keys in every table, not just [project].
defmodule Cure.ProjectSetEditionTest do
  use ExUnit.Case, async: true

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_setedition_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  defp write_toml(dir, body) do
    path = Path.join(dir, "Cure.toml")
    File.write!(path, body)
    path
  end

  defp project_table_count(out), do: length(Regex.scan(~r/^\s*\[project\]/m, out))

  test "F10a: inserts edition under a [project] header carrying a trailing comment", %{dir: dir} do
    path = write_toml(dir, "[project] # my project\nname = \"x\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    out = File.read!(path)
    assert project_table_count(out) == 1
    assert out =~ ~r/edition = "2026"/
  end

  test "F10b: does not rewrite an edition key living in another table", %{dir: dir} do
    path =
      write_toml(
        dir,
        "[project]\nname = \"x\"\nedition = \"2026\"\n\n[dependencies]\nedition = \"do-not-touch\"\n"
      )

    assert :ok = Cure.Project.set_edition(path, "2027")
    out = File.read!(path)
    assert out =~ ~r/edition = "do-not-touch"/
    assert out =~ ~r/\[project\][\s\S]*edition = "2027"/
    refute out =~ ~r/edition = "2026"/
  end

  test "inserts edition into a plain [project] table that lacks one", %{dir: dir} do
    path = write_toml(dir, "[project]\nname = \"x\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    out = File.read!(path)
    assert out =~ ~r/edition = "2026"/
    assert project_table_count(out) == 1
  end

  test "replaces an existing project edition in place", %{dir: dir} do
    path = write_toml(dir, "[project]\nname = \"x\"\nedition = \"2026\"\n")
    assert :ok = Cure.Project.set_edition(path, "2027")
    out = File.read!(path)
    assert out =~ ~r/edition = "2027"/
    refute out =~ ~r/edition = "2026"/
  end

  # Iteration 13 (audit): set_edition/2 documents a "lossless line edit" but the
  # existing-key replacement rewrote the whole line to the bare `edition = "X"`,
  # dropping a trailing inline comment. The sibling migrate writer
  # (replace_leading_pragma_line) preserves trailing text; the two must agree.
  test "preserves a trailing comment on the edition line when replacing", %{dir: dir} do
    path = write_toml(dir, "[project]\nname = \"x\"\nedition = \"2026\"  # pinned\n")
    assert :ok = Cure.Project.set_edition(path, "2027")
    out = File.read!(path)
    assert out =~ ~r/edition = "2027"  # pinned/
    refute out =~ ~r/edition = "2026"/
  end

  # I1 (audit iteration 2): the write side accepted a `[project]` header carrying
  # a trailing comment, but the loader required the line to END with `]`, so the
  # written edition was silently dropped on read-back. Round-trip through load —
  # not just the file text — to pin write/read grammar agreement.
  test "I1: edition written under a comment-trailing [project] header round-trips through load",
       %{dir: dir} do
    write_toml(dir, "[project] # my project\nname = \"x\"\n")
    path = Path.join(dir, "Cure.toml")
    assert :ok = Cure.Project.set_edition(path, "2026")
    assert {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  # A plain [project] table (no comment) must likewise round-trip — guards the
  # loader-grammar change against regressing the ordinary case.
  test "I1: edition written under a plain [project] header round-trips through load", %{dir: dir} do
    write_toml(dir, "[project]\nname = \"x\"\n")
    path = Path.join(dir, "Cure.toml")
    assert :ok = Cure.Project.set_edition(path, "2026")
    assert {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  # I1b (audit iteration 3): the iteration-2 loader regex was `$`-anchored to
  # exactly `[name]`, so it stopped recognising a TOML array-of-tables header
  # `[[deps]]` as a section boundary — its keys then leaked into the preceding
  # [project] table. The writer's `table_header?` still treated `[[deps]]` as a
  # boundary, so writer and loader disagreed again. Read back the project edition
  # through load: the dependency's edition key must NOT leak in.
  test "I1b: an array-of-tables header bounds the section; its keys do not leak into [project]",
       %{dir: dir} do
    write_toml(
      dir,
      "[project]\nname = \"x\"\nedition = \"2026\"\n\n[[dependencies]]\nedition = \"do-not-touch\"\n"
    )

    assert {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  test "I1b: set_edition with an array-of-tables present targets [project] and round-trips",
       %{dir: dir} do
    write_toml(
      dir,
      "[project]\nname = \"x\"\nedition = \"2026\"\n\n[[dependencies]]\nedition = \"do-not-touch\"\n"
    )

    path = Path.join(dir, "Cure.toml")
    assert :ok = Cure.Project.set_edition(path, "2026")
    out = File.read!(path)
    assert out =~ ~r/edition = "do-not-touch"/
    assert {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  # I1c (audit iteration 3): the loader tolerated internal whitespace in a header
  # (`[ project ]` → the "project" table via trim), but the writer's
  # `project_header?` required literal `[project]`, so set_edition failed to find
  # the header and prepended a DUPLICATE `[project]` table. Unify the grammar:
  # set_edition must edit the existing `[ project ]` in place — no bare duplicate.
  test "I1c: set_edition finds a [ project ] header with internal whitespace (no duplicate)",
       %{dir: dir} do
    path = write_toml(dir, "[ project ]\nname = \"x\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    out = File.read!(path)
    refute out =~ ~r/^\[project\]$/m
    assert {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end
end
