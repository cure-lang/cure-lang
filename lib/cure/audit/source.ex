defmodule Cure.Audit.Source do
  @moduledoc """
  Locate a stdlib module's source by its declared `mod` header.

  The filename does not determine the module name — `Std.NonEmpty` lives in
  `non_empty.cure` and `Std.CRDT` in `crdt.cure` — so the header is authoritative.
  """

  @std_dir Path.expand("../../../lib/std", __DIR__)

  @doc """
  The absolute stdlib source directory this module was compiled against. Baked
  at compile time, so it points at the real checkout regardless of the caller's
  working directory. The CLI seeds it into `Cure.Stdlib.Paths`' import resolver
  so a module's `use Std.X` imports resolve from any CWD (see the audit CLI).
  """
  @spec std_dir() :: Path.t()
  def std_dir, do: @std_dir

  @doc """
  The stdlib dir the CLI should seed into `Cure.Stdlib.Paths`' import resolver,
  or `nil` when one already resolves.

  Guards on the fully-RESOLVED source dir (`Cure.Stdlib.Paths.source_dir/0`,
  which honors `CURE_HOME`/`CURE_LIB`/bundled/CWD), NOT just the Application-env
  override. Seeding on the narrower check would fire even when a user pointed
  `CURE_HOME` at a different stdlib and — because the seed lands in the resolver's
  first-priority slot — silently outrank it, auditing the wrong code.
  """
  @spec import_seed_dir(Path.t() | nil) :: Path.t() | nil
  def import_seed_dir(resolved \\ Cure.Stdlib.Paths.source_dir()) do
    if is_nil(resolved), do: std_dir(), else: nil
  end

  @spec locate(String.t()) :: {:ok, Path.t()} | {:error, :not_found}
  def locate(module) do
    pattern = ~r/^\s*mod\s+#{Regex.escape(module)}\s*$/m

    Path.join(@std_dir, "*.cure")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.find(fn path -> Regex.match?(pattern, File.read!(path)) end)
    |> case do
      nil -> {:error, :not_found}
      path -> {:ok, path}
    end
  end
end
