defmodule Cure.Project do
  @moduledoc """
  Cure project management: parse Cure.toml, resolve dependencies,
  scaffold new projects.

  ## Cure.toml Format

      [project]
      name = "my_app"
      version = "0.1.0"

      [dependencies]
      utils = { path = "../shared/utils" }

      [compiler]
      type_check = true
      optimize = true

  ## Application and release sections (v0.26.0)

  A project that ships an `app` macro may additionally declare:

      [application]
      name           = "my_app"
      vsn            = "0.1.0"
      description    = ""
      applications   = ["logger", "crypto"]
      included_applications = []
      start_phases   = ["init", "warm_cache"]

      [application.env]
      port = 4000

      [release]
      name         = "my_app"
      vsn          = "0.1.0"
      include_erts = false
      applications = ["logger"]
      vm_args      = "rel/vm.args"
      sys_config   = "rel/sys.config"

  The parser accepts a minimal TOML subset: scalar string/bool/int
  values, string arrays, and nested tables (`[application.env]`).
  """

  require Logger

  defstruct [
    :name,
    :version,
    :edition,
    dependencies: [],
    compiler_opts: [],
    source_paths: ["lib"],
    root: ".",
    application: nil,
    release: nil,
    doc: nil,
    publish: nil,
    exports: %{modules: []}
  ]

  @type dep :: %{name: String.t(), path: String.t()} | %{name: String.t(), git: String.t(), tag: String.t()}
  @type t :: %__MODULE__{}

  # -- Loading -----------------------------------------------------------------

  @doc """
  The directory of the nearest ancestor `Cure.toml`, starting from the directory
  containing `file_path` and walking up to the filesystem root — or `nil` if no
  ancestor holds a `Cure.toml`. Mirrors how Cargo/npm locate the enclosing
  project: the NEAREST manifest wins, so a file deep in a dependency tree binds to
  its own project's manifest, not a far-away app's (spec §3.2 edition precedence).
  """
  @spec find_root(String.t() | nil) :: String.t() | nil
  def find_root(nil), do: nil

  def find_root(file_path) when is_binary(file_path) do
    file_path |> Path.expand() |> Path.dirname() |> find_root_from_dir()
  end

  defp find_root_from_dir(dir) do
    parent = Path.dirname(dir)

    cond do
      File.regular?(Path.join(dir, "Cure.toml")) ->
        dir

      # Do not ESCAPE the enclosing git repository: a `Cure.toml` above the repo
      # (a sibling/parent project, or a stray `~/Cure.toml`) is unrelated, and
      # binding a file to it would let a stranger's edition silently drive — or,
      # with a typo, spuriously fail — this repo's builds. `.git` marks the repo
      # root (a normal clone: a directory; a git worktree: a file), so stop here
      # with no manifest found rather than walking further up.
      File.exists?(Path.join(dir, ".git")) ->
        nil

      # `Path.dirname/1` is a fixpoint at the filesystem root ("/" -> "/"), so
      # stop there rather than looping forever when no manifest exists above.
      parent == dir ->
        nil

      true ->
        find_root_from_dir(parent)
    end
  end

  @doc "Load a Cure.toml from the given directory (or current dir)."
  @spec load(String.t()) :: {:ok, t()} | {:error, term()}
  def load(dir \\ ".") do
    path = Path.join(dir, "Cure.toml")

    case File.read(path) do
      {:ok, content} ->
        project = parse_toml(content)

        case project.edition do
          nil ->
            {:ok, %{project | root: dir}}

          ed ->
            case Cure.Edition.parse(ed) do
              {:ok, _} -> {:ok, %{project | root: dir}}
              {:error, _} = err -> err
            end
        end

      {:error, :enoent} ->
        {:error, :no_project_file}

      {:error, reason} ->
        {:error, {:file_error, reason}}
    end
  end

  @doc """
  Insert or replace `edition = "<edition>"` under the `[project]` table of the
  `Cure.toml` at `path`, preserving all other lines. Lossless line edit — does
  not reformat the file.
  """
  @spec set_edition(Path.t(), Cure.Edition.t()) :: :ok | {:error, term()}
  def set_edition(path, edition) do
    with {:ok, body} <- File.read(path) do
      lines = String.split(body, "\n")
      new = upsert_edition(lines, edition)
      File.write(path, Enum.join(new, "\n"))
    end
  end

  # Table-aware upsert (F10): only the [project] table's `edition` key is touched.
  # An `edition =` key in another table (e.g. [dependencies]) is left alone, and a
  # [project] header carrying a trailing comment is recognised (no duplicate table).
  defp upsert_edition(lines, edition) do
    kv = "edition = \"#{edition}\""

    case Enum.find_index(lines, &project_header?/1) do
      nil ->
        ["[project]", kv | lines]

      hidx ->
        {head, [header | after_header]} = Enum.split(lines, hidx)
        {section, tail} = Enum.split_while(after_header, &(not table_header?(&1)))
        head ++ [header | edition_in_section(section, kv, edition)] ++ tail
    end
  end

  # Set the edition within the [project] section. If any `edition =` key is
  # present, replace EVERY one (a malformed duplicate would otherwise leave a
  # stale value that the last-write-wins loader reads back); if none, insert the
  # key right after the header. Keys in later tables are outside `section` and
  # are never touched.
  defp edition_in_section(section, kv, edition) do
    if Enum.any?(section, &edition_key?/1) do
      Enum.map(section, fn line ->
        if edition_key?(line), do: replace_edition_value(line, kv, edition), else: line
      end)
    else
      [kv | section]
    end
  end

  # Rewrite only the VALUE of an existing `edition =` line, preserving leading
  # indentation and any trailing inline comment — a lossless line edit, matching
  # the migrate writer `Cure.CLI.replace_leading_pragma_line/2`. Falls back to the
  # canonical `kv` when the line's value is not a simple quoted string (a
  # malformed line the last-write-wins loader would reject anyway).
  defp replace_edition_value(line, kv, edition) do
    case Regex.run(~r/^(\s*edition\s*=\s*)"[^"]*"(.*)$/, line) do
      [_, prefix, rest] -> prefix <> "\"#{edition}\"" <> rest
      nil -> kv
    end
  end

  # All three header predicates derive from ONE grammar (`table_header_name/1`)
  # so the set_edition writer and the loader can never disagree about what a
  # table boundary is (the I1/I1b/I1c bug class). `table_header?` is any header;
  # `project_header?` is the [project] table specifically (name == "project",
  # excluding dotted subtables like `[project.env]`).
  defp table_header?(line), do: table_header_name(line) != nil
  defp project_header?(line), do: table_header_name(line) == "project"
  defp edition_key?(line), do: Regex.match?(~r/^\s*edition\s*=/, line)

  # -- Dependency Resolution ---------------------------------------------------

  @doc """
  Resolve and compile all dependencies for a project.

  The dependency kind dispatches per entry:

  - `path: "..."`   -- local path dependency; compiled in place.
  - `git:  "..."`   -- git dependency; cloned under `_build/deps/<name>`.
  - otherwise       -- registry dependency; resolved via
    `Cure.Project.Registry`, hash-checked, signature-verified, and
    unpacked under `_build/deps/<name>-<version>/`.

  Returns `:ok` on success, `{:error, term}` on the first hard
  failure. Transparency-log failures degrade to a warning unless
  `config :cure, strict_transparency: true` is set.
  """
  @spec resolve_deps(t()) :: :ok | {:error, term()}
  def resolve_deps(%__MODULE__{dependencies: deps, root: root}) do
    # Preferentially reuse the lockfile: if every locked version still
    # satisfies the current constraints, we skip the resolver entirely.
    registry_deps = Enum.filter(deps, &registry_dep?/1)
    top_constraints = for d <- registry_deps, into: %{}, do: {d.name, Map.get(d, :constraint, "")}

    reuse_lock? =
      case Cure.Project.Lock.read(root) do
        {:ok, lock} ->
          match?({:ok, _}, Cure.Project.Lock.resolve_with_lock(top_constraints, lock))

        _ ->
          false
      end

    result =
      Enum.reduce_while(deps, :ok, fn dep, :ok ->
        case resolve_one(dep, root, reuse_lock?) do
          :ok -> {:cont, :ok}
          {:error, _} = err -> {:halt, err}
        end
      end)

    result
  end

  defp registry_dep?(dep) do
    is_nil(Map.get(dep, :path)) and is_nil(Map.get(dep, :git))
  end

  @doc false
  # The project dir a dependency source at `file` resolves its edition against:
  # the nearest ancestor directory holding a `Cure.toml`, walking up from the
  # file but NEVER above `base` (the dependency's extraction/checkout root). This
  # honours a dep that ships its own Cure.toml even under a nested layout
  # (`base/<pkg>-<vsn>/Cure.toml`, which `Cure.Project.load` reads directly and
  # would otherwise miss with a fixed `project_dir: base`), while the base bound
  # guarantees a manifest-less dep never inherits the CONSUMER's edition (A1-F1).
  @spec dep_project_dir(String.t(), String.t()) :: String.t()
  def dep_project_dir(file, base) do
    base = Path.expand(base)
    file |> Path.expand() |> Path.dirname() |> find_dep_root(base)
  end

  defp find_dep_root(dir, base) do
    cond do
      File.regular?(Path.join(dir, "Cure.toml")) -> dir
      dir == base -> base
      # Defensive: a file under `base` reaches `base` exactly on the way up, but
      # if we ever step above it, stop rather than escape into the consumer tree.
      not String.starts_with?(dir <> "/", base <> "/") -> base
      true -> dir |> Path.dirname() |> find_dep_root(base)
    end
  end

  defp resolve_one(%{path: rel_path, name: name}, root, _reuse_lock?)
       when is_binary(rel_path) do
    # A whitespace-only path is a malformed dependency, not a real path — the
    # literal `!= ""` guard alone let it through and it would "resolve" to zero
    # files (A1-F3). Trim before deciding; an all-blank path is rejected like "".
    if String.trim(rel_path) == "" do
      {:error, {:invalid_dependency, name}}
    else
      resolve_path_dep(rel_path, name, root)
    end
  end

  # A blank OR whitespace-only `git` is a malformed dependency. `parse_dep_line`
  # captures the quoted URL verbatim (no trim), so `git = "   "` reaches here as a
  # binary; the literal `!= ""` guard alone let it slip into System.cmd, cloning
  # nothing and silently "resolving" to :ok. Trim before deciding — mirroring the
  # path clause above so both malformed-dep guards agree.
  defp resolve_one(%{git: url, name: name} = dep, root, _reuse_lock?) when is_binary(url) do
    if String.trim(url) == "" do
      {:error, {:invalid_dependency, name}}
    else
      resolve_git_dep(dep, root)
    end
  end

  defp resolve_one(%{name: name} = dep, root, reuse_lock?) do
    version = Map.get(dep, :version)
    constraint = Map.get(dep, :constraint) || version || ">= 0.0.0"
    resolve_registry_dep(name, constraint, root, reuse_lock?)
  end

  defp resolve_one(_, _root, _reuse_lock?), do: :ok

  defp resolve_path_dep(rel_path, name, root) do
    abs_path = Path.expand(rel_path, root)
    cure_files = Path.wildcard(Path.join(abs_path, "lib/**/*.cure"))
    dep_ebin = Path.join(root, "_build/deps/#{name}")
    File.mkdir_p!(dep_ebin)

    with :ok <- compile_dep_files(cure_files, name, dep_ebin, abs_path),
         {:ok, set} <- Cure.Compiler.Artifacts.open_verified_set(dep_ebin) do
      Cure.Compiler.Artifacts.load_verified_set(set.artifact_root)
    end
  end

  @doc """
  Return the source roots of installed dependencies.

  Path dependencies resolve directly from their package `lib/` directory.
  Git and registry dependencies resolve from their installed `_build/deps`
  trees. The result is deterministic and contains only existing directories.
  """
  @spec dependency_source_paths(t()) :: [Path.t()]
  def dependency_source_paths(%__MODULE__{dependencies: deps, root: root}) do
    deps
    |> Enum.flat_map(fn dep ->
      name = Map.get(dep, :name, "")

      cond do
        is_binary(Map.get(dep, :path)) and String.trim(dep.path) != "" ->
          [Path.join(Path.expand(dep.path, root), "lib")]

        is_binary(Map.get(dep, :git)) and String.trim(dep.git) != "" ->
          [Path.join([root, "_build", "deps", name, "lib"])]

        true ->
          Path.wildcard(Path.join([root, "_build", "deps", "#{name}-*", "**", "lib"]))
      end
    end)
    |> Enum.map(&Path.expand/1)
    |> Enum.filter(&File.dir?/1)
    |> Enum.uniq()
    |> Enum.sort()
  end

  @doc "Return installed dependency BEAM directories for runtime/codegen loading."
  @spec dependency_ebin_paths(t()) :: [Path.t()]
  def dependency_ebin_paths(%__MODULE__{dependencies: deps, root: root}) do
    deps
    |> Enum.flat_map(fn dep ->
      name = Map.get(dep, :name, "")

      if is_binary(Map.get(dep, :path)) or is_binary(Map.get(dep, :git)) do
        [Path.join([root, "_build", "deps", name])]
      else
        Path.wildcard(Path.join([root, "_build", "deps", "#{name}-*", "ebin"]))
      end
    end)
    |> Enum.map(&Path.expand/1)
    |> Enum.filter(&File.dir?/1)
    |> Enum.map(&Cure.Compiler.Artifacts.Writer.resolve/1)
    |> Enum.uniq()
    |> Enum.sort()
  end

  # Compile a dependency's sources, each under its OWN edition (dep_project_dir,
  # bounded at `base`, so it honours the dep's own Cure.toml — nested or not — yet
  # never inherits the consumer's edition). Most compile errors stay non-fatal (a
  # dep may ship files the consumer never exercises, matching the historic `_ =`
  # behaviour), but an UNKNOWN-EDITION error is FATAL and loud (A3-F1): a typo'd
  # dep edition must brick the build, not silently emit no beams and surface later
  # as opaque missing-module errors.
  defp compile_dep_files(cure_files, name, dep_ebin, base) do
    package_exports = dependency_exports(cure_files, name, base)

    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           package: name,
           package_exports: package_exports,
           source_paths: cure_files,
           source_roots: [Path.join(base, "lib")],
           output_dir: dep_ebin,
           kind: :dependency,
           repair: true,
           project_dir: base
         ) do
      {:ok, _result} ->
        :ok

      {:error, {:artifact_sweep_failed, errors}} ->
        case Enum.find_value(errors, fn
               {_file, {:edition_error, reason}} -> reason
               _ -> nil
             end) do
          nil -> {:error, {:dependency_compile_failed, name, errors}}
          reason -> {:error, {:dependency_edition_error, name, reason}}
        end

      {:error, reason} ->
        {:error, {:dependency_compile_graph_error, name, reason}}
    end
  end

  defp dependency_exports([], _name, _base), do: %{}

  defp dependency_exports(cure_files, name, base) do
    project_dir = dep_project_dir(List.first(cure_files), base)

    case load(project_dir) do
      {:ok, %{exports: %{modules: modules}}} when is_list(modules) ->
        %{name => Enum.sort(Enum.uniq(modules))}

      _ ->
        %{}
    end
  end

  defp resolve_registry_dep(name, constraint, root, reuse_lock?) do
    with {:ok, version_string, sha} <- pick_version(name, constraint, root, reuse_lock?),
         {:ok, bytes, _hash} <- Cure.Project.Registry.fetch_tarball(name, version_string, sha),
         :ok <- verify_bundle(name, version_string, sha, bytes),
         :ok <- install_tarball(name, version_string, bytes, root) do
      :ok
    else
      {:error, _} = err -> err
    end
  end

  defp pick_version(name, constraint, root, true) do
    # Lock-preferred path: read the lockfile, honour the pinned version.
    case Cure.Project.Lock.read(root) do
      {:ok, lock} ->
        case Map.get(lock, name) do
          %{version: v, hash: h} when is_binary(h) and h != "" ->
            {:ok, v, strip_sha_prefix(h)}

          _ ->
            pick_version(name, constraint, root, false)
        end

      _ ->
        pick_version(name, constraint, root, false)
    end
  end

  defp pick_version(name, _constraint, _root, false) do
    with {:ok, versions} <- Cure.Project.Registry.list_versions(name),
         [top | _] <- versions do
      {:ok, top.version, String.downcase(top.sha256)}
    else
      [] -> {:error, {:no_versions, name}}
      {:error, _} = err -> err
    end
  end

  defp verify_bundle(name, version, _sha, bytes) do
    case Cure.Project.Transparency.verify(name, version, :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)) do
      :ok -> :ok
      {:ok, :unverified} -> :ok
      {:error, _} = err -> err
    end
  end

  defp install_tarball(name, version, bytes, root) do
    target = Path.join(root, "_build/deps/#{name}-#{version}")
    File.mkdir_p!(target)
    tmp = Path.join(target, "pkg.tar.gz")
    File.write!(tmp, bytes)
    _ = :erl_tar.extract(String.to_charlist(tmp), [:compressed, cwd: String.to_charlist(target)])
    _ = File.rm(tmp)

    cure_files = Path.wildcard(Path.join(target, "**/lib/**/*.cure"))
    dep_ebin = Path.join(root, "_build/deps/#{name}-#{version}/ebin")
    File.mkdir_p!(dep_ebin)

    # Edition-per-package: each file resolves under the dep's own Cure.toml even in
    # the common nested layout (target/<pkg>-<vsn>/Cure.toml, which the `**/lib/**`
    # glob anticipates), bounded at `target`; an unknown dep edition fails loudly.
    with :ok <- compile_dep_files(cure_files, name, dep_ebin, target) do
      with {:ok, set} <- Cure.Compiler.Artifacts.open_verified_set(dep_ebin) do
        Cure.Compiler.Artifacts.load_verified_set(set.artifact_root)
      end
    end
  end

  defp strip_sha_prefix("sha256:" <> rest), do: rest
  defp strip_sha_prefix(other), do: other

  # -- Scaffolding -------------------------------------------------------------

  @doc """
  Create a new Cure project in the given directory.

  Equivalent to `scaffold(name, :lib)`.
  """
  @spec init(String.t()) :: :ok
  def init(name), do: scaffold(name, :lib)

  @doc """
  Scaffold a new Cure project from a template.

  Templates:
  - `:lib` -- a basic library project (default).
  - `:app` -- a library project plus a runnable `main` and a test file.
  - `:fsm` -- a project with a starter FSM definition.
  """
  @spec scaffold(String.t(), :lib | :app | :fsm) :: :ok
  def scaffold(name, template \\ :lib) do
    File.mkdir_p!(name)
    File.mkdir_p!(Path.join(name, "lib"))
    File.mkdir_p!(Path.join(name, "test"))

    File.write!(Path.join(name, "Cure.toml"), default_toml(name, template))
    File.write!(Path.join(name, ".gitignore"), default_gitignore())
    File.write!(Path.join(name, "README.md"), default_readme(name))

    case template do
      :lib -> write_lib_template(name)
      :app -> write_app_template(name)
      :fsm -> write_fsm_template(name)
      _ -> write_lib_template(name)
    end

    :ok
  end

  defp default_toml(name, :app) do
    mod = String.capitalize(name)

    """
    [project]
    name = "#{name}"
    version = "0.1.0"

    [dependencies]

    [compiler]
    type_check = false
    optimize = false
    # stdlib_path = "/path/to/cure/ebin"

    [application]
    name           = "#{name}"
    vsn            = "0.1.0"
    description    = ""
    applications   = ["logger"]
    start_phases   = []

    [application.env]

    [release]
    name         = "#{name}"
    vsn          = "0.1.0"
    include_erts = false
    applications = []

    # The `app` macro in lib/app.cure is `app #{mod}`; the
    # compiler verifies that its name matches `[application].name`
    # above.
    """
  end

  defp default_toml(name, _template) do
    """
    [project]
    name = "#{name}"
    version = "0.1.0"

    [dependencies]

    [compiler]
    type_check = false
    optimize = false
    # stdlib_path = "/path/to/cure/ebin"
    """
  end

  defp default_gitignore do
    """
    /_build/
    /Cure.lock
    *.beam
    """
  end

  defp default_readme(name) do
    """
    # #{name}

    A Cure project.

        cure compile lib/
        cure test
        cure run lib/main.cure
    """
  end

  defp write_lib_template(name) do
    mod = String.capitalize(name)

    File.write!(Path.join([name, "lib", "main.cure"]), """
    mod #{mod}
      ## Public entry point.
      fn hello() -> String = "hello from #{name}"
    """)

    File.write!(Path.join([name, "test", "main_test.cure"]), """
    mod #{mod}.Test
      use Std.Test

      fn test_hello() -> Atom =
        Std.Test.assert_eq(#{mod}.hello(), "hello from #{name}")
    """)
  end

  defp write_app_template(name) do
    write_lib_template(name)
    mod = String.capitalize(name)

    File.write!(Path.join([name, "lib", "root_sup.cure"]), """
    ## Root supervisor for the #{mod} application. Add child specs as
    ## the project grows.
    sup #{mod}.Root
      strategy = :one_for_one
      intensity = 3
      period = 5
      children
    """)

    File.write!(Path.join([name, "lib", "app.cure"]), """
    ## #{mod} application.
    ##
    ## Compiles to `:"Cure.App.#{mod}"`, an OTP `Application` callback
    ## module. The compiler verifies that exactly one `app` macro
    ## exists in the project and that its name matches
    ## `[application].name` in `Cure.toml`.
    app #{mod}
      vsn         = "0.1.0"
      description = "#{mod}"
      root        = sup #{mod}.Root
    """)
  end

  defp write_fsm_template(name) do
    write_lib_template(name)
    mod = String.capitalize(name)

    File.write!(Path.join([name, "lib", "fsm.cure"]), """
    mod #{mod}

      fsm Fsm
        state Atom
        events
          Tick -> :keep_state_and_data
    """)
  end

  # -- Lockfile ----------------------------------------------------------------

  @doc """
  Write a Cure.lock file capturing the current resolved dependency set.

  The lockfile format is intentionally simple: one TOML table per
  dependency.
  """
  @spec write_lock(t()) :: :ok
  def write_lock(%__MODULE__{dependencies: deps, root: root}) do
    body =
      Enum.map_join(deps, "\n", fn dep ->
        name = Map.get(dep, :name, "")

        kv =
          ["path", "git", "tag", "ref"]
          |> Enum.flat_map(fn k ->
            v = Map.get(dep, String.to_atom(k))
            if v in [nil, ""], do: [], else: ["  #{k} = \"#{v}\""]
          end)
          |> Enum.join("\n")

        "[lock.#{name}]\n#{kv}"
      end)

    File.write!(Path.join(root, "Cure.lock"), body <> "\n")
  end

  @doc "Render a human-readable dependency tree."
  @spec dep_tree(t()) :: String.t()
  def dep_tree(%__MODULE__{name: name, dependencies: deps}) do
    header = "#{name}"

    children =
      Enum.map(deps, fn dep ->
        kind =
          cond do
            Map.get(dep, :path) -> "path:#{dep.path}"
            Map.get(dep, :git) -> "git:#{dep.git}"
            true -> "unknown"
          end

        "  - #{Map.get(dep, :name)} (#{kind})"
      end)

    Enum.join([header | children], "\n")
  end

  @doc """
  Resolve a git-based dependency by cloning into `_build/deps/<name>` if not
  already present, then compiling its `lib/`.
  """
  @spec resolve_git_dep(map(), String.t()) :: :ok | {:error, term()}
  def resolve_git_dep(%{name: name, git: url} = dep, root) do
    # `cmd_deps_update` calls this DIRECTLY (bypassing resolve_one's trim guard),
    # so the blank/whitespace-URL rejection must live here too — otherwise a
    # `git = "   "` dep clones nothing and silently "resolves" to :ok.
    if is_binary(url) and String.trim(url) != "" do
      target = Path.join(root, "_build/deps/#{name}")

      with :ok <- ensure_clone(dep, url, target, name) do
        cure_files = Path.wildcard(Path.join(target, "lib/**/*.cure"))
        dep_ebin = Path.join(root, "_build/deps/#{name}")

        # Route through the shared helper so a git dep also resolves under its OWN
        # edition (dep_project_dir bounded at `target`, honouring a nested manifest)
        # rather than relying solely on find_root stopping at the clone's `.git`,
        # and so an unknown dep edition fails loudly (A3-F1) — consistent with
        # path/tarball.
        with :ok <- compile_dep_files(cure_files, name, dep_ebin, target),
             {:ok, set} <- Cure.Compiler.Artifacts.open_verified_set(dep_ebin) do
          Cure.Compiler.Artifacts.load_verified_set(set.artifact_root)
        end
      end
    else
      {:error, {:invalid_dependency, name}}
    end
  end

  # Clone the git dep unless it is already present. `System.cmd`'s exit status was
  # previously discarded, so ANY failed clone (unreachable URL, bad tag, network
  # error) left an empty dir → zero .cure files → a silent `:ok` "resolution".
  # Fail loudly on a non-zero clone.
  defp ensure_clone(dep, url, target, name) do
    if File.dir?(Path.join(target, ".git")) do
      :ok
    else
      File.mkdir_p!(target)
      args = ["clone", "--depth", "1"] ++ ref_args(dep) ++ [url, target]

      case System.cmd("git", args, stderr_to_stdout: true) do
        {_out, 0} -> :ok
        {out, _nonzero} -> {:error, {:dependency_clone_failed, name, out}}
      end
    end
  end

  defp ref_args(%{tag: tag}) when is_binary(tag) and tag != "", do: ["--branch", tag]
  defp ref_args(%{ref: ref}) when is_binary(ref) and ref != "", do: ["--branch", ref]
  defp ref_args(_), do: []

  # -- Compiler Options --------------------------------------------------------

  @doc "Get compiler options from the project config."
  @spec compiler_opts(t()) :: keyword()
  def compiler_opts(%__MODULE__{compiler_opts: opts}) do
    [
      check_types: Keyword.get(opts, :type_check, false),
      optimize: Keyword.get(opts, :optimize, false)
    ]
  end

  @doc """
  Return the stdlib BEAM directory configured in `[compiler] stdlib_path`,
  or fall back to `$CURE_LIB` if the key is absent.

  Returns `nil` when neither source provides a value.
  """
  @spec stdlib_path(t()) :: String.t() | nil
  def stdlib_path(%__MODULE__{compiler_opts: opts}) do
    case Keyword.get(opts, :stdlib_path) do
      path when is_binary(path) and path != "" -> path
      _ -> Cure.Stdlib.Paths.cure_lib()
    end
  end

  # -- Project-wide compile driver (v0.26.0) ---------------------------------

  @doc """
  Compile every `.cure` file under the project's `lib/` directory,
  enforcing the single-`app` invariant and emitting a `<name>.app`
  resource file when an `app` macro is present.

  Steps:

  1. Lex+parse every candidate file with a lightweight pre-pass
     looking for lifted application modules.
  2. If more than one `app` is found, return
     `{:error, {:duplicate_app, [{path, name}, ...]}}` (surfaced as
     `E051`).
  3. If exactly one `app` is found, verify its name matches
     `[application].name` (or falls back to `[project].name`).
     Mismatch returns `{:error, {:app_name_mismatch, expected, actual}}`.
  4. Compile every file via `Cure.Compiler.compile_file/2`, threading
     the declared phases through so `Cure.App.Verifier` can report
     start-phase mismatches at compile time.
  5. Emit the `.app` resource alongside the compiled `.beam` files.

  Returns `{:ok, %{modules: [...], app_module: atom() | nil}}` on
  success, `{:error, reason}` otherwise.
  """
  @spec compile_project(t(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def compile_project(%__MODULE__{} = project, opts \\ []) do
    output_dir =
      Keyword.get(opts, :output_dir, Path.join(project.root, "_build/cure/project/ebin"))

    extra_paths =
      Keyword.get_lazy(opts, :paths, fn -> default_source_paths(project) end)

    emit_events? = Keyword.get(opts, :emit_events, false)
    check? = Keyword.get(opts, :check_types, false)

    # Ensure the stdlib is loaded before compiling project files so that
    # `use Std.XXX` imports resolve. The project's [compiler] stdlib_path
    # takes priority; falls back to $CURE_LIB, then the default chain.
    preload_opts = [kind: :all]

    preload_opts =
      case stdlib_path(project) do
        path when is_binary(path) and path != "" ->
          Keyword.put(preload_opts, :stdlib_ebin, path)

        _ ->
          preload_opts
      end

    discovered =
      extra_paths
      |> Enum.flat_map(fn dir ->
        if File.dir?(dir), do: Path.wildcard(Path.join(dir, "**/*.cure")), else: []
      end)

    cure_files_result = {:ok, Enum.sort(discovered)}

    with {:ok, dependency_sets} <- dependency_artifact_sets(project),
         :ok <- Cure.Stdlib.Preload.preload(preload_opts),
         :ok <- load_dependency_sets(dependency_sets),
         {:ok, cure_files} <- cure_files_result,
         {:ok, app_info} <- detect_app(cure_files, project),
         :ok <- verify_app_name(app_info, project),
         {:ok, modules} <-
           compile_all_files(
             cure_files,
             output_dir,
             emit_events?,
             check?,
             declared_phases(project),
             extra_paths,
             project.root,
             dependency_sets
           ),
         :ok <- maybe_write_app_resource(app_info, modules, project, output_dir) do
      {:ok, %{modules: modules, app_module: app_module(app_info)}}
    end
  end

  defp render_host_diagnostic(reason, path) do
    {diagnostic, registry} = Cure.Diagnostic.Host.to_diagnostic(reason, path)

    Cure.Diagnostic.Sink.new(format: :plain, color: :never, width: 80, registry: registry)
    |> Cure.Diagnostic.Sink.render(diagnostic)
  end

  @doc false
  @spec detect_app([String.t()], t()) :: {:ok, map() | nil} | {:error, term()}
  def detect_app(files, _project) do
    # Lex+parse only enough to find lifted application modules. We intentionally
    # emit no events during the pre-pass so the main compile pass
    # remains the sole emitter for LSP consumers.
    # Thread a project-root → edition cache so a project of N files sharing one
    # Cure.toml parses+validates that manifest ONCE, not N times (A1-F4).
    {applications, _cache} =
      Enum.flat_map_reduce(files, %{}, fn file, cache ->
        case File.read(file) do
          {:ok, source} ->
            # Resolve each file's edition (pragma > its project's Cure.toml >
            # default) so the pre-pass reads it against the SAME keyword set the
            # real compile pass will (A2-F2). Without this the pre-pass lexed under
            # current(), so a file pinned to an older edition that used a since-
            # retired keyword would fail to parse here, get swallowed below, and go
            # invisible to app detection while the real compile parsed it fine.
            {edition, cache} = app_pre_pass_edition(source, file, cache)

            result =
              with {:ok, tokens} <-
                     Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false, edition: edition),
                   {:ok, ast} <-
                     Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false, edition: edition) do
                find_application_modules(ast, file)
              else
                _ -> []
              end

            {result, cache}

          _ ->
            {[], cache}
        end
      end)

    case applications do
      [] ->
        {:ok, nil}

      [single] ->
        {:ok, single}

      multiple ->
        {:error, {:duplicate_app, Enum.map(multiple, fn c -> {c.file, c.name} end)}}
    end
  end

  # Edition for a single file in the app-detection pre-pass: its `@edition` pragma,
  # else its project's Cure.toml (the nearest ancestor, bounded at the repo root),
  # else the compiler default. An unknown edition degrades to the default here (the
  # real compile pass reports it loudly); the pre-pass must never crash a build.
  #
  # The per-file pragma is checked FIRST (cheap regex) so a pragma'd file never
  # triggers `find_root`; only a pragma-less file consults the project manifest,
  # and that result is memoised by project root in `cache` (A1-F4) — equivalent to
  # the old `resolve(%{source, project_dir: find_root(file)})` but without re-
  # reading the same Cure.toml once per file.
  defp app_pre_pass_edition(source, file, cache) do
    case Cure.Edition.pragma_edition(source) do
      nil ->
        root = find_root(file)

        case Map.fetch(cache, root) do
          {:ok, ed} ->
            {ed, cache}

          :error ->
            ed =
              case Cure.Edition.resolve(%{project_dir: root}) do
                {:ok, e} -> e
                {:error, _} -> Cure.Edition.current()
              end

            {ed, Map.put(cache, root, ed)}
        end

      pragma ->
        ed =
          case Cure.Edition.parse(pragma) do
            {:ok, e} -> e
            {:error, _} -> Cure.Edition.current()
          end

        {ed, cache}
    end
  end

  defp default_source_paths(%__MODULE__{root: root, source_paths: paths}) do
    Enum.map(paths || ["lib"], &Path.join(root, &1))
  end

  defp find_application_modules({:lift_module, meta, _body}, file) when is_list(meta) do
    if Keyword.get(meta, :behaviour) == :application do
      case Keyword.get(meta, :module) do
        "Cure.App." <> name -> [%{file: file, name: name, meta: meta}]
        _ -> []
      end
    else
      []
    end
  end

  defp find_application_modules({:block, _, children}, file) when is_list(children) do
    Enum.flat_map(children, &find_application_modules(&1, file))
  end

  defp find_application_modules(_, _), do: []

  defp verify_app_name(nil, _project), do: :ok

  defp verify_app_name(%{name: name}, project) do
    expected = app_name_for(project)
    actual = normalize_app_name(name)

    if expected == actual do
      :ok
    else
      {:error, {:app_name_mismatch, expected, actual}}
    end
  end

  @doc false
  def app_name_for(%__MODULE__{} = project) do
    case project.application do
      %{name: n} when is_binary(n) and n != "" -> normalize_app_name(n)
      _ -> normalize_app_name(project.name)
    end
  end

  defp normalize_app_name(nil), do: ""

  defp normalize_app_name(name) when is_binary(name) do
    name
    |> String.replace(".", "_")
    |> Macro.underscore()
  end

  defp declared_phases(%__MODULE__{application: %{start_phases: phases}}) when is_list(phases),
    do: phases

  defp declared_phases(_), do: nil

  defp compile_all_files(
         files,
         output_dir,
         emit?,
         check?,
         declared_phases,
         source_roots,
         diagnostic_path,
         dependency_sets
       ) do
    base_opts = [emit_events: emit?, check_types: check?]

    opts =
      if is_list(declared_phases),
        do: Keyword.put(base_opts, :declared_phases, declared_phases),
        else: base_opts

    case Cure.Compiler.Artifacts.sweep(
           module_pipeline: :canonical,
           source_roots: source_roots,
           source_paths: files,
           output_dir: output_dir,
           kind: :project,
           repair: true,
           stdlib_artifact_digest: Cure.Compiler.Artifacts.stdlib_fingerprint(),
           verify_stdlib: true,
           package_artifact_sets: dependency_sets,
           package_artifact_digests: Map.new(dependency_sets, fn {name, set} -> {name, set.artifact_digest} end),
           package_exports: dependency_exports(dependency_sets),
           compile_opts: opts
         ) do
      {:ok, result} ->
        Enum.each(result.cycles, fn walk ->
          Logger.warning(render_host_diagnostic({:import_cycle, walk}, diagnostic_path))
        end)

        with {:ok, set} <- Cure.Compiler.Artifacts.open_verified_set(output_dir) do
          modules =
            set.modules
            |> Map.keys()
            |> Enum.sort()
            |> Enum.map(&String.to_atom("Cure." <> &1))

          {:ok, modules}
        end

      {:error, {:artifact_sweep_failed, [{_target, reason} | _]}} ->
        {:error, {:compile_failed, reason}}

      {:error, reason} ->
        {:error, {:compile_failed, reason}}
    end
  end

  @doc "Open every installed Cure dependency as one complete verified artifact set."
  @spec dependency_artifact_sets(t()) :: {:ok, map()} | {:error, term()}
  def dependency_artifact_sets(project) do
    project.dependencies
    |> Enum.reduce_while({:ok, %{}}, fn dependency, {:ok, sets} ->
      name = Map.get(dependency, :name, "")
      roots = dependency_ebin_roots(dependency, project.root)

      if roots == [] do
        {:halt, {:error, {:dependency_artifact_set_missing, {:package, name}}}}
      else
        Enum.reduce_while(roots, {:ok, sets}, fn root, {:ok, accumulated} ->
          case Cure.Compiler.Artifacts.open_verified_set(root) do
            {:ok, set} ->
              key = if Map.has_key?(accumulated, name), do: "#{name}@#{root}", else: name

              dependency_set = %{
                root: root,
                artifact_digest: set.artifact_digest,
                exports: Map.get(set.context, :package_exports, %{})
              }

              {:cont, {:ok, Map.put(accumulated, key, dependency_set)}}

            {:error, reason} ->
              {:halt, {:error, {:dependency_artifact_set_invalid, {:package, name}, reason}}}
          end
        end)
        |> case do
          {:ok, accumulated} -> {:cont, {:ok, accumulated}}
          {:error, _reason} = error -> {:halt, error}
        end
      end
    end)
  end

  defp dependency_exports(sets) when is_map(sets) do
    Enum.reduce(sets, %{}, fn {name, set}, exports ->
      Map.merge(exports, Map.get(set, :exports, %{}))
      |> Map.put_new(name, [])
    end)
  end

  defp load_dependency_sets(sets) do
    Enum.reduce_while(sets, :ok, fn {name, %{root: root}}, :ok ->
      case Cure.Compiler.Artifacts.load_verified_set(root) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:dependency_artifact_set_invalid, {:package, name}, reason}}}
      end
    end)
  end

  defp dependency_ebin_roots(dependency, root) do
    name = Map.get(dependency, :name, "")

    roots =
      if is_binary(Map.get(dependency, :path)) or is_binary(Map.get(dependency, :git)) do
        [Path.join([root, "_build", "deps", name])]
      else
        Path.wildcard(Path.join([root, "_build", "deps", "#{name}-*", "ebin"]))
      end

    roots
    |> Enum.map(&Path.expand/1)
    |> Enum.filter(&File.dir?/1)
    |> Enum.map(&Cure.Compiler.Artifacts.Writer.resolve/1)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp app_module(nil), do: nil

  defp app_module(%{name: name}) do
    String.to_atom("Cure.App." <> name)
  end

  defp maybe_write_app_resource(nil, _modules, _project, _output_dir), do: :ok

  defp maybe_write_app_resource(app_info, modules, project, output_dir) do
    Cure.App.Resource.write(app_info, modules, project, output_dir: output_dir)
  end

  # -- TOML Parser (minimal subset) -------------------------------------------

  defp parse_toml(content) do
    lines = String.split(content, "\n")

    acc = %{
      project: %{},
      deps: [],
      compiler: [],
      application: %{},
      release: %{},
      doc: %{},
      doc_groups: %{},
      publish: %{},
      exports: %{}
    }

    parsed = parse_lines(lines, nil, acc)

    application_map = normalize_application(parsed.application)
    release_map = normalize_release(parsed.release)
    doc_map = normalize_doc(parsed.doc, parsed.doc_groups)
    publish_map = normalize_publish(parsed.publish)
    exports_map = normalize_exports(parsed.exports)

    source_paths =
      case Map.get(parsed.project, "source_paths") do
        list when is_list(list) and list != [] -> Enum.map(list, &to_string/1)
        _ -> ["lib"]
      end

    %__MODULE__{
      name: Map.get(parsed.project, "name", "unnamed"),
      version: Map.get(parsed.project, "version", "0.1.0"),
      edition: Map.get(parsed.project, "edition"),
      dependencies: parsed.deps,
      compiler_opts: parsed.compiler,
      source_paths: source_paths,
      application: application_map,
      release: release_map,
      doc: doc_map,
      publish: publish_map,
      exports: exports_map
    }
  end

  defp parse_lines([], _section, acc), do: acc

  defp parse_lines([line | rest], section, acc) do
    trimmed = String.trim(line)

    cond do
      trimmed == "" or String.starts_with?(trimmed, "#") ->
        parse_lines(rest, section, acc)

      header = table_header_name(trimmed) ->
        parse_lines(rest, {:table, header}, acc)

      true ->
        acc = apply_kv(section, trimmed, acc)
        parse_lines(rest, section, acc)
    end
  end

  # A table header line, tolerating an inline comment after the `]` (valid TOML,
  # e.g. `[project] # my project`). Returns the header name, or nil if the line
  # is not a header. Kept consistent with the `set_edition` writer grammar so a
  # header this loader accepts is one the writer will also target (and vice
  # versa) — otherwise a written `edition` would be dropped on read-back.
  defp table_header_name(line) do
    # `\[{1,2}..\]{1,2}` recognises both a table header `[name]` and a TOML
    # array-of-tables header `[[name]]` (the latter is still a section boundary —
    # dropping it would leak its keys into the preceding table). `\s*(?:#.*)?$`
    # tolerates an inline comment. Trimmed internally so the writer's boundary
    # predicates can call this on raw lines.
    case Regex.run(~r/^\[{1,2}([^\]]*)\]{1,2}\s*(?:#.*)?$/, String.trim(line)) do
      [_, name] -> String.trim(name)
      nil -> nil
    end
  end

  defp apply_kv({:table, "project"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {key, val} ->
        # `source_paths = ["a", "b"]` is the only project-level key that
        # currently expects a non-scalar value; route it through
        # `parse_scalar/1` so the array form parses, while every other
        # field stays a plain string with quotes stripped.
        value =
          case key do
            "source_paths" -> parse_scalar(val)
            _ -> strip_quotes(val)
          end

        %{acc | project: Map.put(acc.project, key, value)}
    end
  end

  defp apply_kv({:table, "dependencies"}, line, acc) do
    case parse_dep_line(line) do
      nil -> acc
      dep -> %{acc | deps: [dep | acc.deps]}
    end
  end

  defp apply_kv({:table, "compiler"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {"stdlib_path", val} ->
        %{acc | compiler: [{:stdlib_path, strip_quotes(val)} | acc.compiler]}

      {key, val} ->
        # Only the boolean flags the compiler actually reads (see compiler_opts/1)
        # are recognized; map those to their atom via a fixed allow-list. Every
        # other key is stored-but-never-consumed, so it is dropped rather than
        # fed through String.to_atom/1 on arbitrary user bytes — which raised on
        # a non-UTF-8 key and interned one permanent atom per distinct key (an
        # atom-table DoS from a large or malicious manifest).
        case compiler_bool_key(key) do
          {:ok, atom_key} ->
            bool_val = strip_quotes(val) == "true"
            %{acc | compiler: [{atom_key, bool_val} | acc.compiler]}

          :error ->
            acc
        end
    end
  end

  defp apply_kv({:table, "application"}, line, acc) do
    case parse_kv(line) do
      {"", _} -> acc
      {key, val} -> %{acc | application: Map.put(acc.application, key, parse_scalar(val))}
    end
  end

  defp apply_kv({:table, "application.env"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {key, val} ->
        env = Map.get(acc.application, "env", %{})
        env = Map.put(env, key, parse_scalar(val))
        %{acc | application: Map.put(acc.application, "env", env)}
    end
  end

  defp apply_kv({:table, "release"}, line, acc) do
    case parse_kv(line) do
      {"", _} -> acc
      {key, val} -> %{acc | release: Map.put(acc.release, key, parse_scalar(val))}
    end
  end

  defp apply_kv({:table, "doc"}, line, acc) do
    case parse_kv(line) do
      {"", _} -> acc
      {key, val} -> %{acc | doc: Map.put(acc.doc, key, parse_scalar(val))}
    end
  end

  defp apply_kv({:table, "publish"}, line, acc) do
    case parse_kv(line) do
      {"", _} -> acc
      {key, val} -> %{acc | publish: Map.put(acc.publish, key, parse_scalar(val))}
    end
  end

  defp apply_kv({:table, "exports"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {"modules", val} ->
        %{acc | exports: Map.put(acc.exports, "modules", parse_scalar(val))}

      _ ->
        acc
    end
  end

  defp apply_kv({:table, "doc.groups_for_modules"}, line, acc) do
    case parse_kv(line) do
      {"", _} ->
        acc

      {key, val} ->
        group_name = strip_quotes(key)
        members = parse_scalar(val)

        members =
          case members do
            list when is_list(list) -> list
            single when is_binary(single) -> [single]
            _ -> []
          end

        %{acc | doc_groups: Map.put(acc.doc_groups, group_name, members)}
    end
  end

  defp apply_kv(_section, _line, acc), do: acc

  # The recognized boolean `[compiler]` keys, as an allow-list. Kept in lockstep
  # with compiler_opts/1 (the only reader of these flags). An unrecognized key is
  # dropped rather than interned via String.to_atom/1 on arbitrary user bytes.
  defp compiler_bool_key("type_check"), do: {:ok, :type_check}
  defp compiler_bool_key("optimize"), do: {:ok, :optimize}
  defp compiler_bool_key(_other), do: :error

  defp parse_kv(line) do
    case String.split(line, "=", parts: 2) do
      [key, val] -> {String.trim(key), val |> strip_inline_comment() |> String.trim()}
      _ -> {"", ""}
    end
  end

  # Drop a TOML inline comment from a value: the first `#` that is NOT inside a
  # double-quoted string begins a comment (a `#` within quotes — e.g. a
  # `"C# rocks"` value — is literal). This mirrors the inline-comment tolerance the
  # table-header parser already has, so a trailing `# note` on a value line does
  # not leak into the value — which for the validated `edition` key would turn a
  # valid `"2026"  # pin` into `2026"  # pin` and hard-fail the load (A2-F1).
  defp strip_inline_comment(val) when is_binary(val) do
    # Scan the value BYTE-WISE, not via String.to_charlist/1: a Cure.toml is
    # arbitrary user bytes and a non-UTF-8 byte (e.g. a latin-1 `café`) made
    # to_charlist raise UnicodeConversionError, crashing every project load. The
    # comment/quote logic only inspects ASCII bytes (`#`, `"`, `\`), so byte
    # iteration is equivalent and preserves all other bytes verbatim.
    val |> scan_inline_comment(false, false, []) |> :erlang.iolist_to_binary()
  end

  # (bytes-kept-reversed accumulator; in_quotes?; escaped?)
  defp scan_inline_comment(<<>>, _in_q, _esc, acc), do: Enum.reverse(acc)

  # Inside a basic string a backslash escapes the next char, so a `\"` does NOT
  # close the string (and a following `#` stays part of the value).
  defp scan_inline_comment(<<?\\, rest::binary>>, true, false, acc),
    do: scan_inline_comment(rest, true, true, [?\\ | acc])

  defp scan_inline_comment(<<ch, rest::binary>>, in_q, true, acc),
    do: scan_inline_comment(rest, in_q, false, [ch | acc])

  defp scan_inline_comment(<<?#, _rest::binary>>, false, false, acc), do: Enum.reverse(acc)

  defp scan_inline_comment(<<?", rest::binary>>, in_q, false, acc),
    do: scan_inline_comment(rest, not in_q, false, [?" | acc])

  defp scan_inline_comment(<<ch, rest::binary>>, in_q, false, acc),
    do: scan_inline_comment(rest, in_q, false, [ch | acc])

  # `parse_kv/1` only ever yields a `{binary, binary}` pair, so every
  # in-tree call site of `strip_quotes/1` and `parse_scalar/1` hands
  # over a binary. The catch-all clauses that used to exist for
  # non-binary fallbacks were dead (dialyzer `pattern_match_cov`);
  # the binary-guarded head below is therefore exhaustive.
  defp strip_quotes(val) when is_binary(val) do
    val
    |> String.trim()
    |> String.trim("\"")
  end

  # Parse a TOML scalar: quoted string, bool, integer, string array, or
  # bare identifier. Anything unrecognised falls back to its trimmed
  # textual form so unknown keys still have *some* value.
  defp parse_scalar(raw) when is_binary(raw) do
    trimmed = String.trim(raw)

    cond do
      String.starts_with?(trimmed, "\"") and String.ends_with?(trimmed, "\"") ->
        String.slice(trimmed, 1..-2//1)

      trimmed in ["true", "false"] ->
        trimmed == "true"

      Regex.match?(~r/^-?\d+$/, trimmed) ->
        String.to_integer(trimmed)

      String.starts_with?(trimmed, "[") and String.ends_with?(trimmed, "]") ->
        inner = String.slice(trimmed, 1..-2//1)

        Regex.scan(~r/"([^"]*)"/, inner)
        |> Enum.map(fn [_, v] -> v end)

      true ->
        trimmed
    end
  end

  defp normalize_application(map) when map == %{} or map == nil, do: nil

  defp normalize_application(map) do
    %{
      name: Map.get(map, "name"),
      vsn: Map.get(map, "vsn"),
      description: Map.get(map, "description", ""),
      applications: list_of_strings(Map.get(map, "applications", [])),
      included_applications: list_of_strings(Map.get(map, "included_applications", [])),
      start_phases: list_of_strings(Map.get(map, "start_phases", [])),
      registered: list_of_strings(Map.get(map, "registered", [])),
      env: Map.get(map, "env", %{})
    }
  end

  defp normalize_release(map) when map == %{} or map == nil, do: nil

  defp normalize_release(map) do
    %{
      name: Map.get(map, "name"),
      vsn: Map.get(map, "vsn"),
      include_erts: Map.get(map, "include_erts", false),
      applications: list_of_strings(Map.get(map, "applications", [])),
      vm_args: Map.get(map, "vm_args"),
      sys_config: Map.get(map, "sys_config")
    }
  end

  @doc false
  # Normalize the `[doc]` and `[doc.groups_for_modules]` TOML tables
  # into a tidy map consumed by `Cure.Doc.HTMLGenerator`. Always
  # returns a map (even when the TOML file had no `[doc]` section) so
  # downstream code never has to nil-check.
  def normalize_doc(map, groups)
      when (is_map(map) or is_nil(map)) and (is_map(groups) or is_nil(groups)) do
    map = map || %{}
    groups = groups || %{}

    %{
      main: Map.get(map, "main"),
      title: Map.get(map, "title"),
      extras: list_of_strings(Map.get(map, "extras", [])),
      logo: Map.get(map, "logo"),
      source_url: Map.get(map, "source_url"),
      source_ref: Map.get(map, "source_ref"),
      groups_for_modules: Enum.map(groups, fn {name, members} -> {name, list_of_strings(members)} end)
    }
  end

  defp normalize_publish(map) when map == %{} or map == nil, do: nil

  defp normalize_publish(map) do
    %{
      include_proofs: Map.get(map, "include_proofs", true)
    }
  end

  defp normalize_exports(map) when map == %{} or map == nil, do: %{modules: []}

  defp normalize_exports(map) do
    %{modules: list_of_strings(Map.get(map, "modules", []))}
  end

  defp list_of_strings(list) when is_list(list), do: Enum.map(list, &to_string/1)
  defp list_of_strings(str) when is_binary(str), do: [str]
  defp list_of_strings(_), do: []

  defp parse_dep_line(line) do
    cond do
      # Inline-table form: foo = { path = "...", version = "..." }
      match = Regex.run(~r/^(\w+)\s*=\s*\{(.+)\}/, line) ->
        [_, name, attrs] = match

        pairs =
          Regex.scan(~r/(\w+)\s*=\s*"([^"]*)"/, attrs)
          |> Enum.map(fn [_, k, v] -> {k, v} end)
          |> Map.new()

        %{
          name: name,
          path: Map.get(pairs, "path"),
          git: Map.get(pairs, "git"),
          tag: Map.get(pairs, "tag"),
          # `ref` was recorded by write_lock and consumed by ref_args/1 but never
          # parsed here, so a `ref =` pin was silently dropped (dep cloned the
          # remote default branch). Extract it so the pin is honoured.
          ref: Map.get(pairs, "ref"),
          version: Map.get(pairs, "version"),
          constraint: Map.get(pairs, "constraint") || Map.get(pairs, "version")
        }

      # Simple registry form: foo = "~> 1.0"
      match = Regex.run(~r/^(\w+)\s*=\s*"([^"]+)"/, line) ->
        [_, name, constraint] = match
        %{name: name, path: nil, git: nil, tag: nil, version: constraint, constraint: constraint}

      true ->
        nil
    end
  end
end
