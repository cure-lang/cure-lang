defmodule Cure.REPL.Config do
  @moduledoc """
  Load REPL configuration from `.cure.repl.toml`.

  The REPL honours the same two-tier lookup as Elixir's IEx does for
  `.iex.exs`:

  1. `./.cure.repl.toml` in the current working directory; if present,
     its values take precedence over the user-wide config.
  2. `~/.cure.repl.toml` as a user-wide default when no project-local
     file is present.

  Both files are optional. When neither exists (or TOML parsing fails),
  `load/0` returns `defaults/0` unchanged.

  ## File format

  The file is TOML 1.0, parsed via `:toml`. The REPL reads the
  `[stdlib]` section with two independent keys:

      # ./.cure.repl.toml or ~/.cure.repl.toml
      [stdlib]
      # Which modules to load into the VM. Default: "all".
      # one of: "none" | "all" | ["core", "collections", ...]
      preload = "all"

      # Which modules to auto-import (inject as `use Std.X`).
      # Default: "none" -- prefer explicit `:use Mod` in the REPL.
      # one of: "none" | "all" | ["core", "collections", ...]
      imports = "none"

  Both keys accept the same `Cure.Stdlib.Preload.kind/0` shape:

    * the string `"none"` -> `:none`
    * the string `"all"` -> `:all`
    * a string naming a single group -> that group atom (e.g. `"core"`
      -> `:core`).
    * an array of group name strings -> the list of the corresponding
      atoms, duplicates stripped; unknown entries are dropped with a
      warning printed to `:stderr` so typos are visible but not fatal.

  Absent or malformed values fall back to their respective defaults
  (`"all"` for `preload`, `"none"` for `imports`).
  """

  alias Cure.Stdlib.Preload

  @config_filename ".cure.repl.toml"

  @typedoc "Normalised REPL configuration."
  @type t :: %{preload: Preload.kind(), imports: Preload.kind()}

  @doc "The default config used when no `.cure.repl.toml` is present."
  @spec defaults() :: t()
  def defaults, do: %{preload: :all, imports: :none}

  @doc """
  Load the REPL config, honouring the cwd-then-home precedence.

  Always returns a map compatible with `t:t/0`; any parse failure or
  unknown key is silently replaced with the default.
  """
  @spec load() :: t()
  def load do
    case config_path() do
      nil ->
        defaults()

      path ->
        case read_toml(path) do
          {:ok, parsed} -> from_parsed(parsed)
          {:error, _} -> defaults()
        end
    end
  end

  @doc """
  Build a config map from an already-parsed TOML document.

  Exposed for tests and for host applications that prefer to load the
  TOML themselves.
  """
  @spec from_parsed(map()) :: t()
  def from_parsed(parsed) when is_map(parsed) do
    stdlib_section = Map.get(parsed, "stdlib", %{})
    # Absent `preload` key defaults to "all" so the VM is always primed.
    preload_kind = parse_stdlib(Map.get(stdlib_section, "preload", "all"))
    # Absent `imports` key defaults to nil -> :none (explicit-over-implicit).
    imports_kind = parse_stdlib(Map.get(stdlib_section, "imports"))
    %{preload: preload_kind, imports: imports_kind}
  end

  def from_parsed(_other), do: defaults()

  @doc """
  Normalise the raw TOML value under `[stdlib] preload` to a
  `Cure.Stdlib.Preload.kind/0`. Returns `:none` for any unrecognised
  shape so the REPL keeps booting.
  """
  @spec parse_stdlib(term()) :: Preload.kind()
  def parse_stdlib(nil), do: :none

  def parse_stdlib(value) when is_binary(value) do
    case normalise_atom(value) do
      :none -> :none
      :all -> :all
      atom when is_atom(atom) -> validated_group(atom)
    end
  end

  def parse_stdlib(values) when is_list(values) do
    groups =
      values
      |> Enum.flat_map(fn
        v when is_binary(v) ->
          case normalise_atom(v) do
            :none ->
              []

            :all ->
              # `:all` inside a list is equivalent to "include everything";
              # short-circuit by flattening to every known group.
              Preload.known_groups()

            atom ->
              case validated_group(atom) do
                :none -> []
                g -> [g]
              end
          end

        _other ->
          warn("Ignoring non-string stdlib group entry")

          []
      end)
      |> Enum.uniq()

    case groups do
      [] -> :none
      [single] -> single
      many -> many
    end
  end

  def parse_stdlib(_other) do
    warn("Ignoring unrecognised `[stdlib] preload` value")

    :none
  end

  # ---------------------------------------------------------------------------
  # Internals
  # ---------------------------------------------------------------------------

  defp config_path do
    cwd_candidate = Path.join(File.cwd!(), @config_filename)
    home_candidate = home_path(@config_filename)

    cond do
      File.regular?(cwd_candidate) -> cwd_candidate
      is_binary(home_candidate) and File.regular?(home_candidate) -> home_candidate
      true -> nil
    end
  end

  defp home_path(filename) do
    # Read $HOME directly rather than going through `System.user_home/0`:
    # the latter is evaluated from `:init.get_argument(:home)` at VM
    # boot, so `System.put_env("HOME", ...)` in a test setup does not
    # affect it. Callers that want a non-default home can set `$HOME`
    # and we will pick it up immediately.
    case System.get_env("HOME") do
      nil ->
        case System.user_home() do
          nil -> nil
          home -> Path.join(home, filename)
        end

      home ->
        Path.join(home, filename)
    end
  end

  defp read_toml(path) do
    with {:ok, binary} <- File.read(path),
         {:ok, parsed} <- decode_toml(binary) do
      {:ok, parsed}
    else
      {:error, reason} = err ->
        warn("failed to parse `#{path}`: #{config_reason(reason)}")
        err
    end
  end

  defp config_reason(:invalid), do: "the TOML document is invalid"
  defp config_reason(:unexpected_eof), do: "the TOML document ended unexpectedly"
  defp config_reason(:enoent), do: "the file could not be read"
  defp config_reason(reason) when is_binary(reason), do: reason
  defp config_reason(_reason), do: "the TOML document is invalid"

  defp decode_toml(binary) when is_binary(binary) do
    # `Toml.decode/1` only returns `{:ok, map}` or `{:error, reason}`;
    # no catch-all clause is needed and Dialyzer flags one as unreachable.
    apply(Toml, :decode, [binary])
  end

  defp normalise_atom(value) when is_binary(value) do
    value
    |> String.trim()
    |> String.downcase()
    |> case do
      "" -> :none
      "none" -> :none
      "all" -> :all
      name -> safe_atom(name)
    end
  end

  defp safe_atom(name) do
    try do
      String.to_existing_atom(name)
    rescue
      ArgumentError ->
        # Group atoms are materialised statically in Preload so they
        # always exist by the time we get here; fall back to `:none`
        # for typos rather than creating a new atom.
        warn("unknown stdlib group: #{inspect(name)}")
        :none
    end
  end

  defp validated_group(atom) when is_atom(atom) do
    if atom in Preload.known_groups() do
      atom
    else
      warn("unknown stdlib group: #{inspect(atom)}")
      :none
    end
  end

  defp warn(message) do
    diagnostic = Cure.Diagnostic.Operational.configuration_warning(message)
    Cure.Diagnostic.Host.emit_diagnostic(diagnostic, output_device: :stderr)
  end
end
