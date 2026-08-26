# Iteration 6 (LATENT-1 residual): a path/tarball dependency compiles under its
# OWN edition (its manifest, or the compiler default), NEVER the consuming
# project's — Rust's edition-per-package rule. Before this fix the dep-compile
# sites in Cure.Project passed no :project_dir, so Cure.Compiler.resolve_edition
# fell back to find_root/1, which walks UP from the dep's own source file. A dep
# that ships without its own Cure.toml (and without a `.git` boundary under
# _build/deps) therefore discovered the CONSUMER's manifest and inherited its
# edition. When that consumer edition is a typo (unknown), the dep compile failed
# silently (errors are swallowed by `_ =`) and its .beam was never produced.
defmodule Cure.Project.DepEditionIsolationTest do
  use ExUnit.Case, async: true

  setup do
    root = Path.join(System.tmp_dir!(), "cure_depiso_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    on_exit(fn -> File.rm_rf!(root) end)
    {:ok, root: root}
  end

  test "a manifest-less path dep compiles under the default edition, not the consumer's typo'd one",
       %{root: root} do
    # Consumer manifest declares an UNKNOWN edition. If the dep inherits it, the
    # dep compile fails and no .beam is emitted.
    File.write!(Path.join(root, "Cure.toml"), "[project]\nname = \"app\"\nedition = \"9999\"\n")

    # Path dep lives INSIDE the consumer tree, ships lib/*.cure but NO Cure.toml.
    dep_lib = Path.join([root, "dep", "lib"])
    File.mkdir_p!(dep_lib)
    File.write!(Path.join(dep_lib, "d.cure"), "mod DepMod\n  fn f() -> Int = 1\n")

    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{path: "dep", name: "mydep"}]
    }

    assert :ok = Cure.Project.resolve_deps(project)

    dep_ebin = Path.join(root, "_build/deps/mydep")
    assert {:ok, artifacts} = Cure.Compiler.Artifacts.open_verified_set(dep_ebin)
    beams = Path.wildcard(Path.join(artifacts.artifact_root, "*.beam"))

    assert beams != [],
           "expected the path dep to compile under the default edition and emit a .beam, " <>
             "but none was produced — it inherited the consumer's unknown edition"
  end

  # Iteration 6 (audit A1-F2): a dependency whose inline table has a present-but-
  # BLANK path (`foo = { path = "" }`) previously routed to the git-clone clause
  # (parse_dep_line always emits a `git: nil` key), building `git clone … nil …`
  # and CRASHING System.cmd with an ArgumentError. A malformed dep must fail with
  # a clean error tuple, not raise.
  test "a dependency with a blank path fails with an error, not a crash", %{root: root} do
    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "bad", path: "", git: nil, tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_deps(project)
  end

  # Iteration 7 (audit A1-F3): the blank-path rejection must also catch a
  # WHITESPACE-only path. `path = "   "` satisfies the `!= ""` guard literally, so
  # it slipped into the path clause, expanded to `<root>/   `, found zero files,
  # and silently "resolved" to :ok — defeating the malformed-dep rejection.
  test "a whitespace-only path is rejected, not silently resolved", %{root: root} do
    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "bad", path: "   ", git: nil, tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_deps(project)
  end

  # Iteration 8 (audit finding 2): the blank-git rejection must also catch a
  # WHITESPACE-only git URL, mirroring the path clause. Only a LITERAL empty `git`
  # was rejected; `git = "   "` satisfied the `is_binary` git clause, reached
  # `System.cmd("git", ["clone", …, "   ", target])` whose result is discarded,
  # cloned nothing, found zero files, and silently "resolved" to :ok.
  test "a whitespace-only git URL is rejected, not silently resolved", %{root: root} do
    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "bad", path: nil, git: "   ", tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_deps(project)
  end

  # Iteration 8: guard that the literal-empty git URL stays rejected after the
  # blank/whitespace clauses were merged into one trim-aware clause.
  test "a literal-empty git URL is rejected", %{root: root} do
    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "bad", path: nil, git: "", tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_deps(project)
  end

  # Iteration 10 (audit): `parse_dep_line` recorded tag/version/constraint but NOT
  # `ref`, even though `ref_args/1` has a live `%{ref: ...}` clause and `write_lock`
  # persists a `ref` row — so a `ref =` pin was silently dropped (the dep cloned the
  # remote default branch while the lockfile claimed a ref).
  test "a git dependency's ref pin is parsed", %{root: root} do
    File.write!(
      Path.join(root, "Cure.toml"),
      "[project]\nname = \"app\"\n\n[dependencies]\n" <>
        "mydep = { git = \"https://example.test/r.git\", ref = \"abc123\" }\n"
    )

    {:ok, project} = Cure.Project.load(root)
    dep = Enum.find(project.dependencies, &(&1.name == "mydep"))

    assert Map.get(dep, :ref) == "abc123"
  end

  # Iteration 9 (audit): `cure deps update` calls `resolve_git_dep/2` DIRECTLY,
  # bypassing `resolve_one`'s trim guard, so the whitespace/empty-git rejection must
  # also live at the `resolve_git_dep` boundary — otherwise `deps update` clones
  # nothing and silently "resolves" to :ok. Test the boundary directly.
  test "resolve_git_dep rejects a whitespace-only git URL", %{root: root} do
    dep = %{name: "bad", git: "   ", path: nil, tag: nil, version: nil, constraint: nil}
    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_git_dep(dep, root)
  end

  test "resolve_git_dep rejects an empty git URL", %{root: root} do
    dep = %{name: "bad", git: "", path: nil, tag: nil, version: nil, constraint: nil}
    assert {:error, {:invalid_dependency, "bad"}} = Cure.Project.resolve_git_dep(dep, root)
  end

  # Iteration 9 (audit): `resolve_git_dep/2` discarded `System.cmd`'s exit status, so
  # ANY failed clone (unreachable URL, bad tag, network error) left an empty dir,
  # found zero .cure files, and silently "resolved" to :ok — a bogus green build.
  # A failed clone must fail loudly.
  test "resolve_git_dep fails loudly when the clone fails", %{root: root} do
    # A syntactically-valid but nonexistent local repo URL: `git clone` exits
    # non-zero immediately (no network, no prompt).
    dep = %{
      name: "bad",
      git: "file://" <> Path.join(root, "nonexistent.git"),
      path: nil,
      tag: nil,
      version: nil,
      constraint: nil
    }

    assert {:error, {:dependency_clone_failed, "bad", _out}} =
             Cure.Project.resolve_git_dep(dep, root)
  end

  # Iteration 7 (audit A3-F1): a dependency whose OWN Cure.toml declares an unknown
  # edition must FAIL LOUDLY, not silently. dep_project_dir now routes the dep's
  # manifest into resolve_edition, so a typo'd dep edition makes compile_file return
  # {:edition_error, …}. That error was discarded (`_ =`), leaving the build green
  # with no beams and only opaque missing-module errors downstream. Propagate it.
  test "a dependency's own unknown edition fails the build loudly", %{root: root} do
    dep = Path.join(root, "dep")
    dep_lib = Path.join(dep, "lib")
    File.mkdir_p!(dep_lib)
    # The DEP ships its own manifest with a typo'd edition.
    File.write!(Path.join(dep, "Cure.toml"), "[project]\nname = \"dep\"\nedition = \"9999\"\n")
    File.write!(Path.join(dep_lib, "d.cure"), "mod DepMod\n  fn f() -> Int = 1\n")

    project = %Cure.Project{
      name: "app",
      root: root,
      dependencies: [%{name: "mydep", path: "dep", git: nil, tag: nil, version: nil, constraint: nil}]
    }

    assert {:error, {:dependency_edition_error, "mydep", {:unknown_edition, "9999"}}} =
             Cure.Project.resolve_deps(project)
  end
end
