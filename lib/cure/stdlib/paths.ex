defmodule Cure.Stdlib.Paths do
  @moduledoc """
  Resolve well-known locations for the Cure standard library.

  The stdlib lives in `lib/std/*.cure` (sources) and
  `_build/cure/ebin/Cure.Std.*.beam` (compiled modules) inside the Cure
  repository, but host applications that depend on `:cure` (for example
  `:cure_site`) cannot rely on either of those paths:

    * their working directory is their own project root, not Cure's;
    * production releases strip the `lib/` source tree and keep only
      compiled beams plus the `priv/` directory;
    * `_build/cure/ebin` is a build-time artefact and never ships
      with an OTP release.

  This module provides resolution functions used by
  the dependent module-interface loader, `Cure.REPL.Docs` (for
  `:doc` rendering), and `Cure.Stdlib.Preload` (for loading the BEAMs
  that back qualified calls like `Std.List.map`). Both sources and
  BEAMs fall through the same pattern of candidates:

  ## Source directories (`source_dirs/0`, `source_dir/0`)

    1. `Application.get_env(:cure, :stdlib_source_dir)` -- explicit
       override configured by the host (useful for tests or unusual
       layouts).
    2. `<priv_dir>/std` where `<priv_dir>` is `:code.priv_dir(:cure)`
       -- the canonical bundled location. Populated at compile time
       by `Mix.Tasks.Cure.BundleStdlib`; available verbatim in
       releases because `priv/` is part of every OTP application.
    3. `$CURE_HOME/priv/std`, then `$CURE_HOME/lib/std` -- locations
       derived from the optional `CURE_HOME` environment variable.
       This is what powers the
       `export CURE_HOME=/path/to/cure && alias cure=$CURE_HOME/cure`
       workflow: the escript can be invoked from any directory and
       still resolve the stdlib without depending on the current
       working directory.
    4. `lib/std` relative to the current working directory -- the
       legacy fallback, kept so Cure's own tests and scripts keep
       working when run straight from the repository checkout.

  ## BEAM directories (`beam_dirs/0`, `beam_dir/0`)

    1. `Application.get_env(:cure, :stdlib_beam_dir)` -- explicit
       override (tests, alternative deployment layouts).
    2. The `_build/cure/ebin` belonging to the checkout that contains this
       module -- the current development generation, including when Cure is a
       path dependency of a nested project.
    3. `<priv_dir>/ebin` -- the canonical bundled location, populated
       by `Mix.Tasks.Cure.BundleStdlibBeams`. Rides along with OTP
       releases the same way `priv/std` does.
    4. `$CURE_HOME/priv/ebin`, then `$CURE_HOME/_build/cure/ebin` --
       locations derived from the `CURE_HOME` environment variable.
       The `priv/ebin` form matches a fully-bundled checkout (the
       output of `mix compile`); the `_build` form matches a fresh
       development checkout that has only ever run
       `mix cure.compile_stdlib`.
    5. `_build/cure/ebin` relative to the current working directory
       -- the legacy `mix cure.compile_stdlib` output, kept so
       checkouts that never produced a `priv/ebin/` bundle still work
       in development.

  Only directories that actually exist on disk are returned.
  """

  @legacy_cwd_source Path.join(["lib", "std"])
  @legacy_cwd_regex_source Path.join(["lib", "std_deps", "regex"])
  @legacy_cwd_beam Path.join(["_build", "cure", "ebin"])
  @checkout_source Path.expand("../../std", __DIR__)
  @checkout_regex_source Path.expand("../../std_deps/regex", __DIR__)
  @checkout_beam Path.expand("../../../_build/cure/ebin", __DIR__)

  @cure_home_env_var "CURE_HOME"
  @cure_lib_env_var "CURE_LIB"
  @source_dir_cache_key {__MODULE__, :source_dir}

  @doc """
  Return every candidate stdlib source directory that currently exists,
  in search order. Callers that want a single canonical dir should use
  `source_dir/0`.
  """
  @spec source_dirs() :: [String.t()]
  def source_dirs do
    source_candidates()
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
    |> Enum.filter(&File.dir?/1)
  end

  @doc "Return foundational and embedded package source directories."
  @spec all_source_dirs() :: [String.t()]
  def all_source_dirs, do: Enum.uniq(source_dirs() ++ embedded_source_dirs())

  @doc "Return source directories for embedded stdlib packages."
  @spec embedded_source_dirs() :: [String.t()]
  def embedded_source_dirs do
    ([@checkout_regex_source, bundled_regex_source_dir()] ++
       cure_home_regex_source_dirs() ++
       launcher_home_regex_source_dirs() ++
       [@legacy_cwd_regex_source])
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
    |> Enum.filter(&File.dir?/1)
  end

  @doc """
  Return the first existing stdlib source directory, or `nil` when no
  candidate exists on disk. A `nil` result means neither Cure nor any
  of its consumers shipped the stdlib sources in a location we can
  discover -- callers should degrade gracefully (empty signature
  bundle, `:not_found` for `:doc`).
  """
  @spec source_dir() :: String.t() | nil
  def source_dir do
    # Module resolution asks this for every imported spelling. Re-probing every
    # candidate through Erlang's single file server turns parallel elaboration
    # into a queue and can push otherwise-fast tests past ExUnit's timeout. A
    # compiler process observes one filesystem snapshot; configuration and cwd
    # are part of the key, so a caller that changes resolution inputs gets a
    # fresh snapshot automatically.
    candidates = source_candidates()
    key = {File.cwd!(), candidates}

    case Process.get(@source_dir_cache_key) do
      {^key, source_dir} ->
        source_dir

      _missing_or_changed ->
        source_dir = List.first(source_dirs())
        Process.put(@source_dir_cache_key, {key, source_dir})
        source_dir
    end
  end

  defp source_candidates do
    [configured_source_dir()] ++
      cure_lib_source_dirs() ++
      [@checkout_source] ++
      [bundled_source_dir()] ++
      cure_home_source_dirs() ++
      launcher_home_source_dirs() ++
      [@legacy_cwd_source]
  end

  @doc """
  Return every candidate stdlib BEAM directory that currently exists,
  in search order. Used by `Cure.Stdlib.Preload` to locate compiled
  `Cure.Std.*.beam` modules in both development checkouts and
  packaged OTP releases. Callers that want a single canonical dir
  should use `beam_dir/0`.
  """
  @spec beam_dirs() :: [String.t()]
  def beam_dirs do
    ([configured_beam_dir()] ++
       cure_lib_beam_dirs() ++
       [@checkout_beam] ++
       [bundled_beam_dir()] ++
       cure_home_beam_dirs() ++
       launcher_home_beam_dirs() ++
       [@legacy_cwd_beam])
    |> Enum.reject(&is_nil/1)
    |> Enum.map(&Cure.Compiler.Artifacts.Writer.resolve/1)
    |> Enum.uniq()
    |> Enum.filter(&File.dir?/1)
  end

  @doc """
  Return the first existing stdlib BEAM directory, or `nil` when no
  candidate is present on disk. A `nil` result means the stdlib
  BEAMs were never bundled and no compile-time fallback exists; the
  REPL will still function for type inference (sources handle that),
  but any `Std.*.y` call will raise `:undef` until BEAMs are made
  available or the source-JIT fallback in `Cure.Stdlib.Preload`
  recovers them.
  """
  @spec beam_dir() :: String.t() | nil
  def beam_dir, do: List.first(beam_dirs())

  @doc """
  Return the stdlib artifact publication directory for a Mix environment.

  Test VMs share one publication root. Its children are immutable,
  content-addressed generations and publication is lock-serialized, so
  concurrent suites can reuse identical interfaces without replacing files
  another VM has loaded. Development and production builds retain the
  historical canonical output.
  """
  @spec build_beam_dir(atom(), term()) :: String.t()
  def build_beam_dir(:test, _identity), do: Path.join(["_build", "cure", "test", "ebin"])

  def build_beam_dir(_environment, _identity), do: @legacy_cwd_beam

  @doc """
  Default destination for `Mix.Tasks.Cure.BundleStdlib` and its
  consumers. Exposed as a function (rather than a module attribute)
  so tests can stub it without pulling in Mix machinery.
  """
  @spec bundle_destination() :: String.t()
  def bundle_destination, do: Path.join(["priv", "std"])

  @doc """
  Default destination for `Mix.Tasks.Cure.BundleStdlibBeams` and its
  consumers. Mirrors `bundle_destination/0` but points at the
  compiled-BEAM staging directory.
  """
  @spec beam_bundle_destination() :: String.t()
  def beam_bundle_destination, do: Path.join(["priv", "ebin"])

  # ---------------------------------------------------------------------------

  @doc false
  @spec configured_source_dir() :: String.t() | nil
  def configured_source_dir do
    case Application.get_env(:cure, :stdlib_source_dir) do
      dir when is_binary(dir) -> dir
      _ -> nil
    end
  end

  # Back-compat alias for external callers that used the pre-`beam`
  # naming. Deprecated but left in place to avoid churning every
  # caller in the same changeset.
  @doc false
  @deprecated "Use configured_source_dir/0"
  @spec configured_dir() :: String.t() | nil
  def configured_dir, do: configured_source_dir()

  @doc false
  @spec bundled_source_dir() :: String.t() | nil
  def bundled_source_dir do
    case :code.priv_dir(:cure) do
      {:error, _} -> nil
      priv -> Path.join(to_string(priv), "std")
    end
  end

  @doc false
  @spec bundled_regex_source_dir() :: String.t() | nil
  def bundled_regex_source_dir do
    case :code.priv_dir(:cure) do
      {:error, _} -> nil
      priv -> Path.join([to_string(priv), "std_deps", "regex"])
    end
  end

  @doc false
  @deprecated "Use bundled_source_dir/0"
  @spec bundled_dir() :: String.t() | nil
  def bundled_dir, do: bundled_source_dir()

  @doc false
  @spec configured_beam_dir() :: String.t() | nil
  def configured_beam_dir do
    case Application.get_env(:cure, :stdlib_beam_dir) do
      dir when is_binary(dir) -> dir
      _ -> nil
    end
  end

  @doc false
  @spec bundled_beam_dir() :: String.t() | nil
  def bundled_beam_dir do
    case :code.priv_dir(:cure) do
      {:error, _} -> nil
      priv -> Path.join(to_string(priv), "ebin")
    end
  end

  @doc """
  Return the value of the `CURE_LIB` environment variable, normalised.

  `CURE_LIB` points directly at a directory containing compiled
  `Cure.Std.*.beam` files. Unlike `CURE_HOME` (which expects a Cure
  checkout root), `CURE_LIB` requires no subdirectory convention: the
  directory itself is placed on the BEAM search list.

  Trailing whitespace is stripped and an empty value is treated as
  unset (returning `nil`).
  """
  @spec cure_lib() :: String.t() | nil
  def cure_lib do
    case System.get_env(@cure_lib_env_var) do
      value when is_binary(value) ->
        case String.trim(value) do
          "" -> nil
          trimmed -> trimmed
        end

      _ ->
        nil
    end
  end

  @doc """
  Return the candidate stdlib BEAM directories derived from
  `CURE_LIB`. The directory itself is used directly (no subdirectory
  convention). Always returns a list (possibly empty).
  """
  @spec cure_lib_beam_dirs() :: [String.t()]
  def cure_lib_beam_dirs do
    case cure_lib() do
      nil -> []
      dir -> [dir]
    end
  end

  @doc """
  Return the candidate stdlib source directories derived from
  `CURE_LIB`. By convention, if `CURE_LIB` points at an ebin-style
  directory the sibling `../std` is checked for sources. Always
  returns a list (possibly empty).
  """
  @spec cure_lib_source_dirs() :: [String.t()]
  def cure_lib_source_dirs do
    case cure_lib() do
      nil -> []
      dir -> [Path.expand(Path.join(dir, "../std"))]
    end
  end

  @doc """
  Return the value of the `CURE_HOME` environment variable, normalised.

  Trailing whitespace is stripped and an empty value is treated as
  unset (returning `nil`). Use this to teach the `cure` escript where
  the canonical Cure checkout lives so it can locate the stdlib
  regardless of the caller's working directory.
  """
  @spec cure_home() :: String.t() | nil
  def cure_home do
    case System.get_env(@cure_home_env_var) do
      value when is_binary(value) ->
        case String.trim(value) do
          "" -> nil
          trimmed -> trimmed
        end

      _ ->
        nil
    end
  end

  @doc """
  Return the candidate stdlib BEAM directories derived from
  `CURE_HOME`, in priority order. Always returns a list (possibly
  empty); callers are expected to filter for existence themselves.
  """
  @spec cure_home_beam_dirs() :: [String.t()]
  def cure_home_beam_dirs do
    case cure_home() do
      nil ->
        []

      home ->
        [
          Path.join([home, "priv", "ebin"]),
          Path.join([home, "_build", "cure", "ebin"])
        ]
    end
  end

  @doc """
  Return the candidate stdlib source directories derived from
  `CURE_HOME`, in priority order. Always returns a list (possibly
  empty); callers are expected to filter for existence themselves.
  """
  @spec cure_home_source_dirs() :: [String.t()]
  def cure_home_source_dirs do
    case cure_home() do
      nil ->
        []

      home ->
        [
          Path.join([home, "priv", "std"]),
          Path.join([home, "lib", "std"])
        ]
    end
  end

  @doc false
  @spec cure_home_regex_source_dirs() :: [String.t()]
  def cure_home_regex_source_dirs do
    case cure_home() do
      nil -> []
      home -> [Path.join([home, "priv", "std_deps", "regex"]), Path.join([home, "lib", "std_deps", "regex"])]
    end
  end

  @doc false
  @spec launcher_home_beam_dirs(charlist() | String.t()) :: [String.t()]
  def launcher_home_beam_dirs(script_name \\ :escript.script_name()) do
    case launcher_home(script_name) do
      nil -> []
      home -> [Path.join([home, "priv", "ebin"]), Path.join([home, "_build", "cure", "ebin"])]
    end
  end

  @doc false
  @spec launcher_home_source_dirs(charlist() | String.t()) :: [String.t()]
  def launcher_home_source_dirs(script_name \\ :escript.script_name()) do
    case launcher_home(script_name) do
      nil -> []
      home -> [Path.join([home, "priv", "std"]), Path.join([home, "lib", "std"])]
    end
  end

  @doc false
  @spec launcher_home_regex_source_dirs(charlist() | String.t()) :: [String.t()]
  def launcher_home_regex_source_dirs(script_name \\ :escript.script_name()) do
    case launcher_home(script_name) do
      nil -> []
      home -> [Path.join([home, "priv", "std_deps", "regex"]), Path.join([home, "lib", "std_deps", "regex"])]
    end
  end

  defp launcher_home(script_name) do
    script_name = to_string(script_name)

    if script_name == "" or String.starts_with?(script_name, "-") do
      nil
    else
      script_name |> Path.expand() |> Path.dirname()
    end
  end
end
