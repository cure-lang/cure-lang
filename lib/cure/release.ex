defmodule Cure.Release do
  @moduledoc """
  Build BEAM releases from a Cure project.

  A release is a self-contained directory layout that `erl` can boot
  without Mix or Elixir. `Cure.Release.build/2` assembles that layout
  from the compiled output of `Cure.Project.compile_project/2`:

      _build/cure/rel/<name>/
        lib/<app>-<vsn>/ebin/*.{beam,app}   # for every included app
        releases/<vsn>/<name>.rel
        releases/<vsn>/start.boot
        releases/<vsn>/start.script
        releases/<vsn>/sys.config
        releases/<vsn>/vm.args
        bin/<name>                          # Unix runner script

  The project's `[release]` table in `Cure.toml` controls the release
  name, version, extra applications, and optional overrides for
  `vm.args` / `sys.config`. ERTS is *not* bundled by default; pass
  `include_erts: true` or set `[release].include_erts = true` to
  include it.

  ## Non-goals (v0.26.0)

    * Hot code upgrades (`appup` / `relup`).
    * Distillery-style tarballs, Docker images, etc.
    * Automatic app closure discovery for arbitrary Hex dependencies
      that are not Cure deps -- users list extras explicitly under
      `[release].applications`.
  """

  @default_vm_args """
  ## vm.args written by Cure.Release. Edit in place or override via
  ## [release].vm_args in Cure.toml.
  -name <%= name %>@127.0.0.1
  -setcookie <%= cookie %>

  ## Disable cookie printing
  +W w

  ## Enable kernel poll and a larger async-thread pool.
  +K true
  +A 64
  """

  @doc """
  Build the release described by the project.

  Returns `{:ok, release_dir}` on success or `{:error, reason}` on
  failure. `release_dir` is the absolute path of the top-level release
  directory (`_build/cure/rel/<name>`).

  ## Options

    * `:output_dir`   -- top-level directory for the release. Defaults
      to `"_build/cure/rel/<name>"` under the project root.
    * `:include_erts` -- whether to bundle ERTS with the release.
      Defaults to `[release].include_erts` (which itself defaults to
      `false`).
    * `:extra_apps`   -- list of atom app names to append to the
      release's top-level applications list.
    * `:overwrite`    -- when `true`, delete the output directory before
      writing. Defaults to `true`.
  """
  @spec build(Cure.Project.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def build(%Cure.Project{} = project, opts \\ []) do
    with {:ok, compile_result} <- compile_project(project, opts),
         {:ok, release} <- resolve_release(project, opts),
         release_dir <- release_dir(project, release, opts),
         :ok <- prepare_output(release_dir, Keyword.get(opts, :overwrite, true)),
         :ok <- copy_applications(release, project, release_dir, opts, compile_result),
         {:ok, rel_path} <- write_rel_file(release, project, release_dir),
         :ok <- make_boot_script(rel_path, release_dir, release),
         :ok <- write_sys_config(release, project, release_dir),
         :ok <- write_vm_args(release, project, release_dir),
         :ok <- write_runner(release, project, release_dir) do
      maybe_copy_erts(release, release_dir, opts)
      {:ok, release_dir}
    end
  end

  # -- Compile project -------------------------------------------------------

  defp compile_project(project, opts) do
    ebin_dir =
      Keyword.get(opts, :ebin_dir, Path.join(project.root, "_build/cure/project/ebin"))

    case Cure.Project.compile_project(project, output_dir: ebin_dir, emit_events: false) do
      {:ok, result} -> {:ok, Map.put(result, :ebin_dir, ebin_dir)}
      {:error, _} = err -> err
    end
  end

  # -- Release resolution ----------------------------------------------------

  defp resolve_release(%Cure.Project{release: nil} = project, opts) do
    # The project does not declare a [release] table; synthesise one
    # from the [project] and [application] sections so `cure release`
    # still works for minimal projects.
    {:ok,
     %{
       name: project_release_name(project, opts),
       vsn: project_version(project),
       include_erts: Keyword.get(opts, :include_erts, false),
       applications: Keyword.get(opts, :extra_apps, []),
       vm_args: nil,
       sys_config: nil
     }}
  end

  defp resolve_release(%Cure.Project{release: release} = project, opts) do
    {:ok,
     %{
       name: release.name || project_release_name(project, opts),
       vsn: release.vsn || project_version(project),
       include_erts:
         case Keyword.fetch(opts, :include_erts) do
           {:ok, v} -> v
           :error -> release.include_erts
         end,
       applications: (release.applications || []) ++ Keyword.get(opts, :extra_apps, []),
       vm_args: release.vm_args,
       sys_config: release.sys_config
     }}
  end

  defp project_release_name(project, opts) do
    Keyword.get(opts, :name) || Cure.Project.app_name_for(project)
  end

  defp project_version(%Cure.Project{application: %{vsn: vsn}}) when is_binary(vsn) and vsn != "",
    do: vsn

  defp project_version(%Cure.Project{version: v}) when is_binary(v) and v != "", do: v
  defp project_version(_), do: "0.1.0"

  defp release_dir(project, release, opts) do
    case Keyword.get(opts, :output_dir) do
      nil -> Path.join([project.root, "_build/cure/rel", release.name])
      dir -> Path.expand(dir)
    end
  end

  defp prepare_output(release_dir, true) do
    _ = File.rm_rf(release_dir)
    File.mkdir_p(release_dir)
  end

  defp prepare_output(release_dir, false) do
    File.mkdir_p(release_dir)
  end

  # -- Application closure + copy -------------------------------------------

  defp copy_applications(release, project, release_dir, _opts, compile_result) do
    closure = application_closure(release, project)

    release_lib = Path.join(release_dir, "lib")
    File.mkdir_p!(release_lib)

    {copied, skipped} =
      Enum.reduce(closure, {[], []}, fn app_atom, {copied, skipped} ->
        case copy_application(app_atom, release_lib, project, compile_result) do
          :ok -> {[app_atom | copied], skipped}
          {:error, {:release_app_missing, app, _reason}} -> {copied, [app | skipped]}
        end
      end)

    # Stash the final app list on the process dictionary so the
    # downstream `.rel` builder and boot-script step only include
    # apps that were actually placed under `release_dir/lib/`.
    Process.put({__MODULE__, :resolved_apps}, Enum.reverse(copied))

    if skipped != [] do
      :logger.warning(~c"cure release: skipping apps that were not loaded: ~p", [skipped])
    end

    with :ok <- copy_verified_stdlib(release_lib, copied),
         :ok <- copy_project_dependencies(release_lib, project) do
      :ok
    end
  end

  defp copy_verified_stdlib(release_lib, copied_apps) do
    if :cure in copied_apps do
      with {:ok, set} <-
             Cure.Compiler.Artifacts.open_verified_set(
               kind: :stdlib,
               candidates: Cure.Stdlib.Paths.beam_dirs()
             ),
           version <- Application.spec(:cure, :vsn) |> to_string(),
           destination <- Path.join([release_lib, "cure-#{version}", "ebin"]),
           {:ok, _copied} <-
             Cure.Compiler.Artifacts.copy_verified_flat(set.artifact_root, destination) do
        :ok
      end
    else
      :ok
    end
  end

  defp copy_project_dependencies(release_lib, project) do
    dependency_roots = Cure.Project.dependency_ebin_paths(project)

    if dependency_roots == [] do
      :ok
    else
      project_app = Cure.Project.app_name_for(project)

      case Path.wildcard(Path.join([release_lib, "#{project_app}-*", "ebin"])) do
        [destination] -> build_release_artifact_set(destination, dependency_roots)
        [] -> {:error, {:release_app_missing, String.to_atom(project_app), :missing_project_ebin}}
        paths -> {:error, {:artifact_error, "Ambiguous project release artifact roots", %{paths: paths}}}
      end
    end
  end

  defp build_release_artifact_set(destination, dependency_roots) do
    with {:ok, project_set} <- Cure.Compiler.Artifacts.open_verified_set(destination) do
      package_artifact_digests =
        case get_in(project_set, [:dependencies, :packages]) do
          generations when is_map(generations) and map_size(generations) > 0 ->
            generations

          _ ->
            %{}
        end

      case Cure.Compiler.Artifacts.merge_verified_flat(
             [destination | dependency_roots],
             destination,
             kind: :release,
             package_artifact_digests: package_artifact_digests
           ) do
        {:ok, _set} -> :ok
        {:error, reason} -> {:error, reason}
      end
    end
  end

  defp resolved_apps(release, project) do
    case Process.get({__MODULE__, :resolved_apps}) do
      nil -> application_closure(release, project)
      apps -> apps
    end
  end

  # Every Cure release implicitly depends on the `cure` application
  # because compiled actors reference `Cure.Actor.State`, compiled
  # supervisors reference `Cure.Sup.Runtime`, and compiled FSMs
  # reference `Cure.FSM.Runtime`. Adding `:cure` (and with it the
  # transitive closure of its runtime) to the defaults makes the
  # generated release self-contained for supervision-tree
  # applications.
  @default_apps ~w(kernel stdlib compiler elixir cure)a

  defp application_closure(release, project) do
    project_app_atom = String.to_atom(Cure.Project.app_name_for(project))

    application_apps =
      case project.application do
        %{applications: apps} when is_list(apps) -> apps
        _ -> []
      end

    seed =
      @default_apps ++
        release.applications ++
        application_apps ++
        maybe_app(project_app_atom)

    seed
    |> Enum.map(&to_existing_atom/1)
    |> Enum.reject(&is_nil/1)
    |> expand_transitive_apps()
    |> Enum.uniq()
  end

  # Walk each seed app's `:applications` key recursively to compute the
  # transitive closure `:systools.make_script/2` requires.
  defp expand_transitive_apps(seed) do
    Enum.reduce(seed, {[], MapSet.new()}, fn app, {acc, seen} ->
      {collected, seen} = collect_app(app, seen)
      {acc ++ collected, seen}
    end)
    |> elem(0)
    |> Enum.uniq()
  end

  defp collect_app(app, seen) do
    if MapSet.member?(seen, app) do
      {[], seen}
    else
      # Ensure the application's .app file is loaded so `spec/2` can
      # return its dependency list. `Application.load/1` is a no-op
      # when the app is already loaded or running.
      _ = Application.load(app)

      deps = Application.spec(app, :applications) || []
      included = Application.spec(app, :included_applications) || []

      Enum.reduce([app | deps ++ included], {[], MapSet.put(seen, app)}, fn a, {acc, s} ->
        {collected, s} =
          if a == app do
            {[app], s}
          else
            collect_app(a, s)
          end

        {acc ++ collected, s}
      end)
    end
  end

  defp maybe_app(atom) when is_atom(atom) do
    if Atom.to_string(atom) == "", do: [], else: [atom]
  end

  defp to_existing_atom(atom) when is_atom(atom), do: atom

  defp to_existing_atom(string) when is_binary(string) do
    try do
      String.to_existing_atom(string)
    rescue
      ArgumentError -> String.to_atom(string)
    end
  end

  defp copy_application(app, release_lib, project, compile_result) do
    case locate_application(app, project, compile_result) do
      {:ok, vsn, {source_ebin, extra_files}} ->
        dest = Path.join(release_lib, "#{app}-#{vsn}/ebin")
        File.mkdir_p!(dest)

        source_ebin
        |> File.ls!()
        |> Enum.each(fn entry ->
          src = Path.join(source_ebin, entry)
          dst = Path.join(dest, entry)
          File.cp!(src, dst)
        end)

        Enum.each(extra_files, fn src ->
          File.cp!(src, Path.join(dest, Path.basename(src)))
        end)

        :ok

      {:ok, vsn, source_ebin} ->
        dest = Path.join(release_lib, "#{app}-#{vsn}/ebin")
        File.mkdir_p!(dest)

        source_ebin
        |> File.ls!()
        |> Enum.each(fn entry ->
          src = Path.join(source_ebin, entry)
          dst = Path.join(dest, entry)
          File.cp!(src, dst)
        end)

        :ok

      {:error, reason} ->
        {:error, {:release_app_missing, app, reason}}
    end
  end

  # Locate an application's ebin directory and vsn. For the project's
  # own app we look in the local `_build/cure/project/ebin`; every other app
  # comes from the currently-loaded code path, which covers the OTP
  # stdlib and every Hex dependency built by Mix.
  defp locate_application(app, project, compile_result) do
    ebin_dir =
      Map.get(
        compile_result,
        :ebin_dir,
        Path.join(project.root, "_build/cure/project/ebin")
      )

    project_app = String.to_atom(Cure.Project.app_name_for(project))

    cond do
      app == project_app ->
        app_path = Path.join(ebin_dir, "#{app}.app")

        if File.exists?(app_path) do
          with {:ok, artifact_set} <-
                 Cure.Compiler.Artifacts.open_verified_set(ebin_dir) do
            vsn = read_app_vsn(app_path)
            {:ok, vsn, {artifact_set.artifact_root, [app_path]}}
          end
        else
          {:error, :missing_app_file}
        end

      true ->
        case Application.spec(app) do
          nil ->
            {:error, :not_loaded}

          spec ->
            vsn = to_string(Keyword.get(spec, :vsn, "0.0.0"))

            case :code.lib_dir(app) do
              {:error, reason} ->
                {:error, reason}

              dir when is_list(dir) ->
                {:ok, vsn, Path.join(List.to_string(dir), "ebin")}
            end
        end
    end
  end

  defp read_app_vsn(app_path) do
    case :file.consult(String.to_charlist(app_path)) do
      {:ok, [{:application, _, props}]} ->
        case Keyword.get(props, :vsn) do
          vsn when is_list(vsn) -> List.to_string(vsn)
          vsn when is_binary(vsn) -> vsn
          _ -> "0.0.0"
        end

      _ ->
        "0.0.0"
    end
  end

  # -- .rel file -------------------------------------------------------------

  defp write_rel_file(release, project, release_dir) do
    releases_dir = Path.join(release_dir, "releases/#{release.vsn}")
    File.mkdir_p!(releases_dir)

    erts_vsn = :erlang.system_info(:version) |> List.to_string()

    rel_apps =
      release
      |> resolved_apps(project)
      |> Enum.map(fn app ->
        vsn =
          case Application.spec(app, :vsn) do
            nil ->
              # project's own app: read from .app file we emitted
              ebin = Path.join(project.root, "_build/cure/project/ebin")
              read_app_vsn(Path.join(ebin, "#{app}.app"))

            v when is_list(v) ->
              List.to_string(v)

            v when is_binary(v) ->
              v
          end

        {app, String.to_charlist(vsn)}
      end)
      |> Enum.uniq_by(&elem(&1, 0))

    rel_term =
      {:release, {String.to_charlist(release.name), String.to_charlist(release.vsn)},
       {:erts, String.to_charlist(erts_vsn)}, rel_apps}

    rel_path = Path.join(releases_dir, "#{release.name}.rel")
    contents = :io_lib.format(~c"~p.~n", [rel_term])
    File.write!(rel_path, IO.iodata_to_binary(contents))

    {:ok, rel_path}
  end

  # -- Boot script -----------------------------------------------------------

  defp make_boot_script(rel_path, release_dir, release) do
    # `:systools` ships with `:sasl`; ensure it is loaded before we
    # reach for `make_script/2`. When the app is already running this
    # is a no-op, and `ensure_all_started/1` never raises on an
    # `:already_started` tag.
    _ = Application.ensure_all_started(:sasl)

    releases_dir = Path.join(release_dir, "releases/#{release.vsn}")
    rel_base = String.replace_suffix(rel_path, ".rel", "")

    # :systools wants path/to/name (without the .rel). The :path must
    # include every lib/<app>-<vsn>/ebin directory we copied.
    paths =
      release_dir
      |> Path.join("lib/*/ebin")
      |> Path.wildcard()
      |> Enum.map(&String.to_charlist/1)

    release_lib = release_dir |> Path.join("lib") |> String.to_charlist()

    opts = [
      {:path, paths},
      {:outdir, String.to_charlist(releases_dir)},
      # Rewrite `$ROOT/lib/<App>-<Vsn>/ebin` references in the boot
      # script to `$RELEASE_LIB/<App>-<Vsn>/ebin`. The runner script
      # passes `-boot_var RELEASE_LIB $RELEASE_ROOT/lib` so the
      # release's own copy of each app is used at boot, instead of
      # the host Erlang's installation paths.
      {:variables, [{~c"RELEASE_LIB", release_lib}]},
      :silent,
      :no_warn_sasl,
      :no_dot_erlang
    ]

    case :systools.make_script(String.to_charlist(rel_base), opts) do
      :ok ->
        :ok

      {:ok, _module, _warnings} ->
        :ok

      {:error, module, reason} ->
        {:error, {:release_build_failed, module, reason}}

      other ->
        {:error, {:release_build_failed, other}}
    end
  end

  # -- sys.config ------------------------------------------------------------

  defp write_sys_config(%{sys_config: src}, project, release_dir) when is_binary(src) do
    src_path = Path.expand(src, project.root)
    dest = Path.join(release_dir, "releases/#{destination_vsn(release_dir)}/sys.config")

    case File.read(src_path) do
      {:ok, contents} ->
        File.write!(dest, contents)
        :ok

      {:error, reason} ->
        {:error, {:sys_config_read_failed, src_path, reason}}
    end
  end

  defp write_sys_config(_release, project, release_dir) do
    dest = Path.join(release_dir, "releases/#{destination_vsn(release_dir)}/sys.config")
    env = (project.application && Map.get(project.application, :env, %{})) || %{}
    app_atom = String.to_atom(Cure.Project.app_name_for(project))

    config_term =
      if env == %{} do
        []
      else
        env_list =
          Enum.map(env, fn {k, v} ->
            key =
              cond do
                is_atom(k) -> k
                is_binary(k) -> String.to_atom(k)
                true -> k
              end

            {key, v}
          end)

        [{app_atom, env_list}]
      end

    contents = :io_lib.format(~c"~p.~n", [config_term])
    File.write!(dest, IO.iodata_to_binary(contents))
    :ok
  end

  defp destination_vsn(release_dir) do
    # The release_dir/releases/ directory always has exactly one vsn
    # subdirectory at this point; use it.
    Path.join(release_dir, "releases")
    |> File.ls!()
    |> List.first() || "0.1.0"
  end

  # -- vm.args ---------------------------------------------------------------

  defp write_vm_args(%{vm_args: src} = release, project, release_dir) when is_binary(src) do
    src_path = Path.expand(src, project.root)
    dest = Path.join(release_dir, "releases/#{release.vsn}/vm.args")

    case File.read(src_path) do
      {:ok, contents} ->
        File.write!(dest, contents)
        :ok

      {:error, reason} ->
        {:error, {:vm_args_read_failed, src_path, reason}}
    end
  end

  defp write_vm_args(release, _project, release_dir) do
    dest = Path.join(release_dir, "releases/#{release.vsn}/vm.args")

    cookie =
      :crypto.strong_rand_bytes(16)
      |> Base.encode16(case: :lower)
      |> String.to_charlist()
      |> List.to_string()

    rendered =
      @default_vm_args
      |> String.replace("<%= name %>", release.name)
      |> String.replace("<%= cookie %>", cookie)

    File.write!(dest, rendered)
    :ok
  end

  # -- Runner script ---------------------------------------------------------

  defp write_runner(release, _project, release_dir) do
    bin_dir = Path.join(release_dir, "bin")
    File.mkdir_p!(bin_dir)

    path = Path.join(bin_dir, release.name)

    script = """
    #!/usr/bin/env sh
    # Generated by Cure.Release. Boots the #{release.name} release.
    set -eu

    SELF_DIR=$(cd "$(dirname "$0")" && pwd)
    RELEASE_ROOT="$(cd "$SELF_DIR/.." && pwd)"
    RELEASE_VSN="#{release.vsn}"
    RELEASE_NAME="#{release.name}"

    ERL="${ERL:-erl}"

    exec "$ERL" \\
      -boot "$RELEASE_ROOT/releases/$RELEASE_VSN/$RELEASE_NAME" \\
      -boot_var RELEASE_LIB "$RELEASE_ROOT/lib" \\
      -config "$RELEASE_ROOT/releases/$RELEASE_VSN/sys.config" \\
      -args_file "$RELEASE_ROOT/releases/$RELEASE_VSN/vm.args" \\
      "$@"
    """

    File.write!(path, script)
    File.chmod!(path, 0o755)
    :ok
  end

  # -- ERTS bundling ---------------------------------------------------------

  defp maybe_copy_erts(%{include_erts: true}, release_dir, _opts) do
    root = :code.root_dir() |> List.to_string()
    vsn = :erlang.system_info(:version) |> List.to_string()
    src = Path.join(root, "erts-#{vsn}")
    dest = Path.join(release_dir, "erts-#{vsn}")

    if File.dir?(src) do
      File.cp_r!(src, dest)
    end

    :ok
  end

  defp maybe_copy_erts(_, _release_dir, _opts), do: :ok
end
