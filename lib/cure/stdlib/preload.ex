defmodule Cure.Stdlib.Preload do
  @moduledoc """
  Load compiled Cure stdlib (and optionally example) BEAM modules into
  the running VM *without* adding their output directory to the global
  Erlang code path.

  ## Why not just `:code.add_patha/1`?

  Historically the preload helpers in `Cure.CLI`,
  `Mix.Tasks.Cure.Check.Examples` and the regression test suite all did:

      :code.add_patha(String.to_charlist(Path.expand("_build/cure/ebin")))

  That is convenient right up until `_build/cure/ebin` contains a stale
  lowercase `<name>.beam` left over from a previous compile with the old
  naming convention (for example, an older `examples/math.cure` produced
  a top-level `math.beam`). The moment the directory is on the code path,
  that stale file takes precedence over OTP's own `:math`, `:code`,
  `:lists`, etc., and any subsequent call to e.g. `:math.pi/0` raises
  `UndefinedFunctionError` because the stale module never exported it.

  Loading the beams directly via `:code.load_binary/3` by their fully
  qualified `Cure.*` names side-steps the whole class of shadowing bugs:
  only modules whose file name starts with `Cure.` are ever considered,
  and the target directory is never added to the global code path.

  ## Module discovery and grouping

  The set of stdlib modules is *not* hard-coded. At Elixir compile time
  this module walks `lib/std/*.cure`, extracts the declared `mod Std.X`
  name, and the first `@group(:<group>)` module-level decorator in each
  source (see `docs/STDLIB.md`). Modules without a `@group` decorator are
  assigned to `:core` by default.

  The resulting `%{module => group}` map is baked into the module via
  `@external_resource` so any change to `lib/std/*.cure` invalidates the
  compile cache. When `lib/std/` is not available (e.g. a packaged
  release), `stdlib_modules/1` opens one verified artifact generation and
  reads each module's `-group([:g]).` BEAM attribute without loading code.

  ## Kinds

  `stdlib_modules/1` and `preload/1` both accept a `kind` argument that
  filters modules by group:

    * `:none` (the default) -- empty list; nothing is loaded unless the
      caller asks for it explicitly.
    * `:all` -- every `Cure.Std.*` module known to the build.
    * `:core | :collections | :text | :numeric | :system |
       :concurrency | :option | :test | :network` -- the modules tagged
      with that group.
    * A list combining any of the group atoms; the union of their
      memberships with duplicates stripped.

  The "explicit over implicit" default means the REPL starts with no
  stdlib modules pre-imported unless `.cure.repl.toml` (or the caller)
  says otherwise; CLI entry points like `cure run` and
  `mix cure.check.examples` pass `kind: :all` to preserve their
  historical behaviour.
  """

  alias Cure.Compiler.Artifacts
  alias Cure.Stdlib.Paths

  @default_examples_ebin "_build/cure/ex_ebin"

  @stdlib_source_dir Path.expand("../../../lib/std", __DIR__)
  @regex_source_dir Path.expand("../../std_deps/regex", __DIR__)
  @stdlib_source_dirs [@stdlib_source_dir, @regex_source_dir]

  @known_groups [
    :core,
    :collections,
    :text,
    :numeric,
    :system,
    :concurrency,
    :option,
    :test,
    :network
  ]

  # ---------------------------------------------------------------------------
  # Compile-time scan of the foundational stdlib and embedded Regex package.
  # ---------------------------------------------------------------------------

  @stdlib_sources @stdlib_source_dirs
                  |> Enum.flat_map(fn source_dir ->
                    case File.ls(source_dir) do
                      {:ok, entries} ->
                        entries
                        |> Enum.filter(&String.ends_with?(&1, ".cure"))
                        |> Enum.map(&Path.join(source_dir, &1))

                      {:error, _} ->
                        []
                    end
                  end)
                  |> Enum.sort()

  for src <- @stdlib_sources do
    @external_resource src
  end

  @mod_regex ~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m
  @group_regex ~r/^\s*@group\(\s*:([a-z_][a-z0-9_]*)\s*\)/m

  # Cure stdlib modules are emitted as plain Erlang-style atoms
  # (`:"Cure.Std.List"`), not as Elixir-prefixed atoms
  # (`:"Elixir.Cure.Std.List"`). The compiler's BEAM output uses the
  # former, so we build the same shape here.
  @std_module_groups (for path <- @stdlib_sources,
                          {:ok, src} <- [File.read(path)],
                          [_, declared] = Regex.run(@mod_regex, src) || [nil, nil],
                          is_binary(declared),
                          into: %{} do
                        module = String.to_atom("Cure." <> declared)

                        group =
                          case Regex.run(@group_regex, src) do
                            [_, g] -> String.to_atom(g)
                            _ -> :core
                          end

                        {module, group}
                      end)

  # Dependency maps baked at compile time via DepGraph (design spec
  # 2026-07-08-auto-import-order §3.3): order-only (`use` edges) and full
  # closure (`use` + qualified-call + auto-prelude). Keys/values are
  # runtime module atoms (:"Cure.Std.X"). Empty when lib/std was absent
  # at compile time (packaged releases) — consumers degrade to plain
  # selection in that case.
  {order_map, closure_map} =
    (fn ->
       # No `known_modules:` needed here: the compile set IS the full
       # stdlib (`@stdlib_sources` already lists every foundational and
       # embedded-package source
       # file), so `DepGraph.scan/2`'s own AST-derived `modules` map
       # already covers every stdlib module name -- there is nothing
       # out-of-set left for `known_modules` to add. (Contrast a scan
       # over a strict subset, or user files needing to recognize
       # `Std.*` qualified calls as legitimate closure deps -- that's
       # the scenario `known_modules` exists for; it isn't this one.)
       case Cure.Compiler.DepGraph.scan(@stdlib_sources) do
         {:ok, graph} ->
           to_atoms = fn map ->
             Map.new(map, fn {k, vs} ->
               {String.to_atom("Cure." <> k), Enum.map(vs, &String.to_atom("Cure." <> &1))}
             end)
           end

           {to_atoms.(Cure.Compiler.DepGraph.order_deps_map(graph)),
            to_atoms.(Cure.Compiler.DepGraph.closure_deps_map(graph))}

         {:error, _} ->
           {%{}, %{}}
       end
     end).()

  @std_order_deps order_map
  @std_closure_deps closure_map

  # ---------------------------------------------------------------------------
  # Public API
  # ---------------------------------------------------------------------------

  @typedoc "A stdlib group atom."
  @type group ::
          :core
          | :collections
          | :text
          | :numeric
          | :system
          | :concurrency
          | :option
          | :test
          | :network

  @typedoc """
  Kind filter understood by `stdlib_modules/1` and `preload/1`.

    * `:none` -- the empty selection (default everywhere).
    * `:all`  -- every known stdlib module.
    * a single `group` atom or a list of them -- the union of the
      modules tagged with any of those groups.
  """
  @type kind :: :all | :none | group() | [group()]

  @typedoc """
  Options for `preload/1`.

    * `:kind` -- which stdlib modules to load (see `t:kind/0`).
      Defaults to `:none` so callers must opt in.
    * `:examples` -- when `true`, also loads every `Cure.*.beam` found in
      the examples output directory. Defaults to `false`.
    * `:stdlib_ebin` -- override the stdlib beam directory. When not
      given, the full candidate list from `Cure.Stdlib.Paths.beam_dirs/0`
      is searched in order (`:cure` env override, bundled
      `priv/ebin`, legacy `_build/cure/ebin`). Passing a string here
      collapses the search to just that directory for callers that
      need deterministic behaviour (tests, scripts).
    * `:examples_ebin` -- override the examples beam directory. Defaults
      to `"_build/cure/ex_ebin"`.
    * `:source_jit` -- when `true` (the default), any module in
      `stdlib_modules(kind)` that failed to load from the BEAM
      candidates is recompiled from its `.cure` source via
      `Cure.Compiler.compile_and_load/2`. Disable for test harnesses
      that want a hard failure if the BEAMs are missing.
  """
  @type option ::
          {:kind, kind()}
          | {:modules, [module()]}
          | {:examples, boolean()}
          | {:stdlib_ebin, String.t()}
          | {:examples_ebin, String.t()}
          | {:source_jit, boolean()}

  @doc """
  Return the canonical list of stdlib group atoms, in a stable order.

  Exposed so `Cure.REPL.Config` can validate user-supplied kinds.
  """
  @spec known_groups() :: [group()]
  def known_groups, do: @known_groups

  @doc """
  Return the baked-in `%{module => group}` map derived from
  `lib/std/*.cure` at Elixir compile time.

  The map is empty when `lib/std/` was unavailable during compilation;
  in that case `stdlib_modules/1` falls back to BEAM introspection.
  """
  @spec module_groups() :: %{module() => group()}
  def module_groups, do: @std_module_groups

  @doc "Baked `use`-only dependency map (module atoms). Empty in beams-only deployments."
  @spec module_order_deps() :: %{module() => [module()]}
  def module_order_deps, do: @std_order_deps

  @doc "Baked full closure dependency map (use + qualified calls + auto-prelude)."
  @spec module_closure_deps() :: %{module() => [module()]}
  def module_closure_deps, do: @std_closure_deps

  # ---------------------------------------------------------------------------
  # Built-in operator fixity table (Phase 3, Task 3.2)
  # ---------------------------------------------------------------------------

  @doc """
  Assemble the built-in operator `Cure.Compiler.Parser.FixityTable` by parsing
  the `Std.Operators` stdlib module (`lib/std/operators.cure`).

  `Std.Operators` declares every built-in operator with the same relative
  binding power and associativity as the legacy static
  `Cure.Compiler.Parser.Precedence` table. This accessor reads those
  `precedencegroup`/`infix`/`prefix`/`postfix` declarations and reduces them
  into a `FixityTable`.

  Purely additive in this task: nothing in the expression parser consults the
  returned table yet (the static `Precedence` module still governs how
  expressions bind). A later Phase-3 task flips the Pratt loop onto it.

  Returns an empty table when the source cannot be found or parsed (e.g. a
  packaged release that ships neither `lib/std/` nor `priv/std/`).
  """
  #
  # The table computation itself now lives in
  # `Cure.Compiler.Parser.BuiltinFixity` (compiler layer) so the parser can reach
  # it during THIS module's own compile-time dependency bake without a load-order
  # cycle. These are thin delegators kept for the public API.
  @spec builtin_fixity_table() :: Cure.Compiler.Parser.FixityTable.t()
  defdelegate builtin_fixity_table(), to: Cure.Compiler.Parser.BuiltinFixity, as: :table

  @doc """
  Extend an existing `FixityTable` with the `precedencegroup`/`infix`/… decls
  found in `ast`. Used by the parser to layer a module's own fixity declarations
  onto the memoized built-in table.
  """
  @spec extend_fixity_table(Cure.Compiler.Parser.FixityTable.t(), term()) ::
          Cure.Compiler.Parser.FixityTable.t()
  defdelegate extend_fixity_table(base, ast), to: Cure.Compiler.Parser.BuiltinFixity, as: :extend

  @doc """
  `stdlib_modules(kind)` expanded to its dependency closure over the baked
  closure map. Selection semantics are unchanged — closure only adds the
  modules the selection needs at runtime. Degrades to the plain selection
  when the baked maps are empty (beams-only deployments).
  """
  @spec closure_modules(kind()) :: [module()]
  def closure_modules(kind) do
    Cure.Compiler.DepGraph.closure(@std_closure_deps, stdlib_modules(kind))
  end

  @doc """
  Return the list of stdlib modules matching `kind`.

  See `t:kind/0` for the accepted values. Default is `:none`.

  ## Examples

      iex> Cure.Stdlib.Preload.stdlib_modules(:none)
      []

      # :core returns modules tagged :core via `@group(:core)`:
      iex> :"Cure.Std.Core" in Cure.Stdlib.Preload.stdlib_modules(:core)
      true
  """
  @spec stdlib_modules(kind()) :: [module()]
  def stdlib_modules(kind \\ :none)

  def stdlib_modules(:none), do: []

  def stdlib_modules(:all), do: all_modules()

  def stdlib_modules(kind) when is_atom(kind) do
    validate_kind!(kind)
    filter_by_groups([kind])
  end

  def stdlib_modules(kinds) when is_list(kinds) do
    Enum.each(kinds, &validate_kind!/1)
    filter_by_groups(Enum.uniq(kinds))
  end

  def stdlib_modules(other) do
    raise ArgumentError, """
    invalid kind: #{inspect(other)}
    expected :all, :none, a group atom, or a list of group atoms.
    known groups: #{inspect(@known_groups)}
    """
  end

  @doc """
  Load compiled stdlib (and optionally example) modules.

  Returns `:ok` only after selecting and verifying one complete artifact
  generation. Invalid or partial candidates return a structured error before
  any module is loaded.

  Resolution order for each module:

    1. Iterate `Cure.Stdlib.Paths.beam_dirs/0` and select the first directory
       whose complete manifest and every claimed BEAM verify.
    2. When repair is enabled and no candidate verifies, rebuild the complete
       stdlib source set through the artifact sweep and verify it again.

  A release carrying sources but no valid generation can therefore recover
  without ever loading an isolated, unmanifested module.

  See `t:option/0` for the accepted options. `:kind` defaults to `:none`
  so the caller must opt into loading.
  """
  @spec preload([option()]) :: :ok | {:error, term()}
  def preload(opts \\ []) do
    kind = Keyword.get(opts, :kind, :none)
    requested_modules = Keyword.get(opts, :modules)
    examples_ebin = Keyword.get(opts, :examples_ebin, @default_examples_ebin)
    include_examples? = Keyword.get(opts, :examples, false)
    source_jit? = Keyword.get(opts, :source_jit, true)

    if kind == :none and is_nil(requested_modules) do
      maybe_load_examples(include_examples?, examples_ebin)
    else
      candidate_dirs = stdlib_candidate_dirs(opts)

      with {:ok, artifact_set} <-
             open_or_repair_stdlib(candidate_dirs, source_jit?, opts),
           :ok <- load_stdlib(artifact_set, kind, requested_modules) do
        maybe_load_examples(include_examples?, examples_ebin)
      end
    end
  end

  # Resolve the list of candidate BEAM directories for this preload
  # call. A caller-supplied `:stdlib_ebin` collapses the search to a
  # single directory (the legacy behaviour), while the default taps
  # into `Cure.Stdlib.Paths.beam_dirs/0` so every layout known to the
  # `Paths` module is consulted.
  defp stdlib_candidate_dirs(opts) do
    case Keyword.get(opts, :stdlib_ebin) do
      nil -> Paths.beam_dirs()
      dir when is_binary(dir) -> Enum.filter([dir], &File.dir?/1)
    end
  end

  # ---------------------------------------------------------------------------
  # Internals
  # ---------------------------------------------------------------------------

  defp validate_kind!(kind) when kind in [:all, :none], do: :ok

  defp validate_kind!(kind) when is_atom(kind) do
    if kind in @known_groups do
      :ok
    else
      raise ArgumentError, """
      unknown stdlib group: #{inspect(kind)}
      known groups: #{inspect(@known_groups)}
      """
    end
  end

  defp validate_kind!(other) do
    raise ArgumentError, "invalid kind entry: #{inspect(other)}"
  end

  defp filter_by_groups(groups) do
    # A plain list suffices here: at most 9 known groups, so `group in
    # wanted` is O(9) in the worst case. Using `MapSet` triggered a
    # Dialyzer `call_without_opaque` warning on the follow-up
    # `MapSet.member?/2` call.
    wanted = Enum.uniq(groups)

    all_modules_with_groups()
    |> Enum.filter(fn {_module, group} -> group in wanted end)
    |> Enum.map(fn {module, _group} -> module end)
    |> Enum.sort()
  end

  defp all_modules do
    all_modules_with_groups()
    |> Enum.map(fn {module, _group} -> module end)
    |> Enum.sort()
  end

  # Prefer the compile-time map; fall back to BEAM introspection when
  # `lib/std/` was unavailable at compile time (packaged releases).
  defp all_modules_with_groups do
    case @std_module_groups do
      map when map_size(map) > 0 ->
        Map.to_list(map)

      _ ->
        case Artifacts.open_verified_set(
               kind: :stdlib,
               candidates: Paths.beam_dirs()
             ) do
          {:ok, set} -> discover_from_beams(set.artifact_root)
          {:error, _reason} -> []
        end
    end
  end

  defp discover_from_beams(ebin) do
    if File.dir?(ebin) do
      ebin
      |> Path.join("Cure.Std.*.beam")
      |> Path.wildcard()
      |> Enum.map(fn path ->
        module =
          path
          |> Path.basename(".beam")
          |> String.to_atom()

        {module, group_from_beam(module, path)}
      end)
    else
      []
    end
  end

  # Read a module's group from its `-group([:g]).` BEAM attribute *without*
  # loading the beam (the chunk is metadata, not code). Falls back to the
  # legacy `__group__/0` export only for stale packaged beams that predate
  # the `@group` decorator, and to `:core` as the final default.
  defp group_from_beam(_module, path) do
    case :beam_lib.chunks(String.to_charlist(path), [:attributes]) do
      {:ok, {_module, [attributes: attrs]}} ->
        case Keyword.get(attrs, :group) do
          [g] when is_atom(g) -> g
          _ -> :core
        end

      _ ->
        :core
    end
  end

  # For each requested module, walk the candidate directories in
  # order and load from the first one that has a readable `.beam`.
  # Missing modules are left unloaded; the source-JIT fallback picks
  # them up later.
  defp load_stdlib(artifact_set, kind, requested_modules) do
    modules =
      case requested_modules do
        nil -> ordered_closure_modules(kind)
        modules -> ordered_requested_modules(modules)
      end

    Artifacts.load_verified_modules(artifact_set.artifact_root, modules)
  end

  # Closure-expanded selection in dependency (use-edge) order. toposort/2
  # is SCC-tolerant, so this always yields a complete deterministic list
  # even if a cycle ever appears in the baked map.
  defp ordered_closure_modules(kind) do
    Cure.Compiler.DepGraph.toposort(@std_order_deps, closure_modules(kind))
  end

  defp ordered_requested_modules(modules) do
    requested = modules |> Enum.filter(&is_atom/1) |> Enum.uniq()
    closure = Cure.Compiler.DepGraph.closure(@std_closure_deps, requested)
    Cure.Compiler.DepGraph.toposort(@std_order_deps, closure)
  end

  defp open_or_repair_stdlib(candidate_dirs, source_jit?, opts) do
    trace_candidate_verification(candidate_dirs)

    case Artifacts.open_verified_set(kind: :stdlib, candidates: candidate_dirs) do
      {:ok, artifact_set} ->
        {:ok, artifact_set}

      {:error, verification_error} when source_jit? ->
        repair_stdlib(candidate_dirs, opts, verification_error)

      {:error, verification_error} ->
        {:error, verification_error}
    end
  end

  defp trace_candidate_verification(candidate_dirs) do
    if System.get_env("CURE_TRACE_STDLIB") in ["1", "true"] do
      Enum.each(candidate_dirs, fn root ->
        result = Artifacts.open_verified_set(root, verification: :full)
        IO.puts(:stderr, "stdlib candidate #{Path.expand(root)}: #{inspect(result, limit: 8)}")
      end)
    end
  end

  defp repair_stdlib(candidate_dirs, opts, verification_error) do
    with source_dir when is_binary(source_dir) <-
           Keyword.get(opts, :stdlib_source_dir) || Paths.source_dir(),
         files when files != [] <- Path.wildcard(Path.join(source_dir, "*.cure")),
         output_dir <- repair_output_dir(candidate_dirs, opts),
         {:ok, summary} <- Cure.Stdlib.Packages.compile(files, output_dir),
         {:ok, artifact_set} <- Artifacts.open_verified_set(summary.artifact_root) do
      {:ok, artifact_set}
    else
      nil -> {:error, {:stdlib_sources_unavailable, verification_error}}
      [] -> {:error, {:stdlib_sources_empty, verification_error}}
      {:error, reason} -> {:error, {:stdlib_repair_failed, reason}}
    end
  end

  defp repair_output_dir(candidate_dirs, opts) do
    Keyword.get(opts, :stdlib_ebin) ||
      List.first(candidate_dirs) ||
      "_build/cure/ebin"
  end

  defp maybe_load_examples(false, _ebin), do: :ok
  defp maybe_load_examples(true, ebin), do: load_cure_beams(ebin)

  # Example artifacts obey the same whole-set rule as the standard library.
  defp load_cure_beams(ebin) do
    with {:ok, artifact_set} <- Artifacts.open_verified_set(ebin) do
      modules =
        artifact_set.modules
        |> Map.values()
        |> Enum.flat_map(&Map.get(&1, :artifacts, []))
        |> Enum.map(&String.to_existing_atom(&1.module))
        |> Enum.uniq()

      Artifacts.load_verified_modules(artifact_set.artifact_root, modules)
    end
  end
end
