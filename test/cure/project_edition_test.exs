defmodule Cure.ProjectEditionTest do
  use ExUnit.Case, async: true

  defp write_toml(body) do
    dir = Path.join(System.tmp_dir!(), "cureproj_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "Cure.toml"), body)
    dir
  end

  # find_root/1 (iteration 5): locate the nearest ancestor Cure.toml from a file
  # path so the compile boundary can honour a project's edition without every CLI
  # caller threading a project dir.
  test "find_root returns the directory of the nearest ancestor Cure.toml" do
    dir = write_toml("[project]\nname = \"demo\"\nedition = \"2026\"\n")
    sub = Path.join([dir, "a", "b"])
    File.mkdir_p!(sub)
    assert Cure.Project.find_root(Path.join(sub, "x.cure")) == Path.expand(dir)
  end

  test "find_root returns the NEAREST manifest when nested (child shadows parent)" do
    parent = write_toml("[project]\nname = \"outer\"\nedition = \"2026\"\n")
    child = Path.join(parent, "inner")
    File.mkdir_p!(child)
    File.write!(Path.join(child, "Cure.toml"), "[project]\nname = \"inner\"\n")
    assert Cure.Project.find_root(Path.join(child, "x.cure")) == Path.expand(child)
  end

  test "find_root returns nil when no ancestor holds a Cure.toml (no loop at fs root)" do
    dir = Path.join(System.tmp_dir!(), "cure_noroot_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    assert Cure.Project.find_root(Path.join(dir, "x.cure")) == nil
  end

  test "find_root(nil) is nil (headless source with no file)" do
    assert Cure.Project.find_root(nil) == nil
  end

  # Iteration 5 audit (Agent B finding 1): the upward walk must not ESCAPE the
  # enclosing git repository. A `Cure.toml` above the repo (a sibling/parent
  # project, or a stray ~/Cure.toml) is unrelated; binding to it would let a
  # stranger's edition silently drive — or, with a typo, spuriously fail — builds
  # of files in this repo. Stop at the dir holding `.git` (a git worktree uses a
  # `.git` FILE, a normal clone a dir — both count).
  test "find_root stops at the git-repo root and does not escape to an ancestor Cure.toml" do
    base = Path.join(System.tmp_dir!(), "cure_gitbound_#{System.unique_integer([:positive])}")
    repo = Path.join(base, "repo")
    src = Path.join(repo, "src")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(base) end)
    # Stray manifest ABOVE the repo boundary; must NOT be discovered.
    File.write!(Path.join(base, "Cure.toml"), "[project]\nname = \"stray\"\nedition = \"9999\"\n")
    # Repo boundary marker (a git worktree writes a `.git` file).
    File.write!(Path.join(repo, ".git"), "gitdir: /wherever\n")

    assert Cure.Project.find_root(Path.join(src, "a.cure")) == nil
  end

  test "find_root still returns a Cure.toml that sits AT the git-repo root" do
    base = Path.join(System.tmp_dir!(), "cure_gitroot_#{System.unique_integer([:positive])}")
    src = Path.join(base, "src")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(base) end)
    File.write!(Path.join(base, ".git"), "gitdir: /wherever\n")
    File.write!(Path.join(base, "Cure.toml"), "[project]\nname = \"ok\"\nedition = \"2026\"\n")

    assert Cure.Project.find_root(Path.join(src, "a.cure")) == Path.expand(base)
  end

  # Iteration 6 (audit A1-F1): a tarball dep extracts under a nested package dir
  # (`target/<pkg>-<vsn>/lib/...`, which the install glob `**/lib/**` anticipates),
  # and `Cure.Project.load` reads `<dir>/Cure.toml` DIRECTLY (no upward walk). A
  # fixed `project_dir: target` therefore missed a nested dep's own Cure.toml and
  # resolved it under the default edition instead of its declared one. dep_project_dir
  # finds the nearest ancestor holding a Cure.toml, bounded at the extraction base so
  # it can never escape into the CONSUMER's tree.
  describe "dep_project_dir/2 (edition-per-package, base-bounded)" do
    defp mk(dir), do: File.mkdir_p!(dir)

    test "finds a NESTED package's own Cure.toml" do
      base = Path.join(System.tmp_dir!(), "cure_depdir_#{System.unique_integer([:positive])}")
      pkg = Path.join(base, "foo-1.0")
      lib = Path.join(pkg, "lib")
      mk(lib)
      on_exit(fn -> File.rm_rf!(base) end)
      File.write!(Path.join(pkg, "Cure.toml"), "[project]\nname = \"foo\"\nedition = \"2026\"\n")

      assert Cure.Project.dep_project_dir(Path.join(lib, "x.cure"), base) == Path.expand(pkg)
    end

    test "returns base for a FLAT layout (Cure.toml at base)" do
      base = Path.join(System.tmp_dir!(), "cure_depdir_#{System.unique_integer([:positive])}")
      lib = Path.join(base, "lib")
      mk(lib)
      on_exit(fn -> File.rm_rf!(base) end)
      File.write!(Path.join(base, "Cure.toml"), "[project]\nname = \"foo\"\nedition = \"2026\"\n")

      assert Cure.Project.dep_project_dir(Path.join(lib, "x.cure"), base) == Path.expand(base)
    end

    test "returns base (→ default edition) when the dep ships NO Cure.toml" do
      base = Path.join(System.tmp_dir!(), "cure_depdir_#{System.unique_integer([:positive])}")
      lib = Path.join([base, "foo-1.0", "lib"])
      mk(lib)
      on_exit(fn -> File.rm_rf!(base) end)

      assert Cure.Project.dep_project_dir(Path.join(lib, "x.cure"), base) == Path.expand(base)
    end

    test "never escapes the base to an ancestor (consumer) Cure.toml" do
      outer = Path.join(System.tmp_dir!(), "cure_depdir_#{System.unique_integer([:positive])}")
      base = Path.join(outer, "dep")
      lib = Path.join(base, "lib")
      mk(lib)
      on_exit(fn -> File.rm_rf!(outer) end)
      # A manifest ABOVE the extraction base (the consumer's) must be ignored.
      File.write!(Path.join(outer, "Cure.toml"), "[project]\nname = \"consumer\"\nedition = \"9999\"\n")

      assert Cure.Project.dep_project_dir(Path.join(lib, "x.cure"), base) == Path.expand(base)
    end
  end

  test "loads a validated edition from the [project] table" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2026\"\n")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  test "absent edition key yields nil (the default path is applied at resolution, not load)" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == nil
  end

  test "an unknown edition in the manifest is a load-time error" do
    dir = write_toml("[project]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2062\"\n")
    assert {:error, {:unknown_edition, "2062"}} = Cure.Project.load(dir)
  end

  # Iteration 6 (audit A2-F1): TOML permits an inline comment after a value, and
  # the header parser already tolerates it (`[project] # note`). A trailing comment
  # on the `edition` value must NOT leak into the value — otherwise a VALID edition
  # (`"2026"  # pin`) becomes `2026"  # pin`, which fails validation and hard-fails
  # the load, breaking the "fail loud only on a genuinely unknown edition" contract.
  test "a trailing inline comment on the edition value is stripped, not a hard fail" do
    dir = write_toml("[project]\nname = \"demo\"\nedition = \"2026\"  # pin the surface\n")
    assert {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
  end

  # A `#` INSIDE the quoted value is not a comment delimiter and must be preserved.
  test "a hash inside a quoted string value is not treated as a comment" do
    dir = write_toml("[project]\nname = \"C# rocks\"\nedition = \"2026\"\n")
    assert {:ok, project} = Cure.Project.load(dir)
    assert project.name == "C# rocks"
  end

  # Iteration 7 (audit A1-F1): the inline-comment stripper must respect backslash
  # escapes inside a basic string. An ESCAPED quote (`\"`) does not close the
  # string, so a `#` that follows it is still inside the value, not a comment.
  # Without escape-awareness, `"a \" b # c"` mis-toggles the quote state at the
  # `\"`, treats the `#` as a comment, and silently truncates the value.
  test "an escaped quote inside a value does not cause a false comment cut" do
    dir = write_toml("[project]\nname = \"a \\\" b # c\"\nedition = \"2026\"\n")
    assert {:ok, project} = Cure.Project.load(dir)

    assert String.contains?(project.name, "# c"),
           "value truncated at # despite the # being inside the string: #{inspect(project.name)}"
  end
end
