defmodule Cure.Oracle do
  @moduledoc """
  Differential oracle for the transliteration program (design spec §7).

  Compares a corpus of paired programs — the same program in Idris surface
  syntax (`.idr`) and Cure surface syntax (`.cure`) — as accept/reject verdicts.
  Two modes: `live` (regenerates `verdicts.json` from `idris2 --check`, driven by
  `mix cure.oracle`) and `replay` (asserts Cure's current verdicts against the
  committed fixtures, no Idris toolchain — `test/oracle_replay_test.exs`).

  The contract is a *relation*, not equality: `same` (default), `cure_stricter`,
  or `idris_only`. Every divergence must carry a written reason; a divergence
  with no recorded reason fails `consistent/1`.
  """

  @root "test/oracle"

  @doc "Cluster names: immediate subdirectories of `test/oracle/`."
  @spec clusters() :: [String.t()]
  def clusters do
    case File.ls(@root) do
      {:ok, entries} -> entries |> Enum.filter(&File.dir?(Path.join(@root, &1))) |> Enum.sort()
      {:error, _} -> []
    end
  end

  @doc "Paired `.cure`/`.idr` probes in a cluster, keyed by shared basename."
  @spec pairs(String.t()) :: [%{name: String.t(), cure_path: String.t(), idr_path: String.t()}]
  def pairs(cluster) do
    dir = Path.join(@root, cluster)

    dir
    |> Path.join("*.cure")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.map(fn cure_path ->
      name = Path.basename(cure_path, ".cure")
      %{name: name, cure_path: cure_path, idr_path: Path.join(dir, name <> ".idr")}
    end)
  end

  @doc "Cure's verdict: does the program elaborate?"
  @spec cure_verdict(String.t()) :: :accept | :reject
  def cure_verdict(cure_path) do
    case Cure.Elab.Program.elaborate(File.read!(cure_path)) do
      {:ok, _env} -> :accept
      {:error, _reason} -> :reject
    end
  end

  @doc """
  `cure_verdict/1` with wall-clock timing and a hard timeout guard. Returns
  `{verdict, elapsed_ms}` where `verdict` is `:accept | :reject | :timeout`.
  A non-terminating elaboration (e.g. a rewrite-bridge loop) is `:brutal_kill`-ed
  at `timeout` and reported as `:timeout` rather than hanging the whole run.
  """
  @spec cure_verdict_timed(String.t(), timeout()) ::
          {:accept | :reject | :timeout, non_neg_integer()}
  def cure_verdict_timed(cure_path, timeout \\ cure_timeout()),
    do: timed(timeout, fn -> cure_verdict(cure_path) end)

  @doc "`idris_verdict/2` with wall-clock timing and a timeout guard. See `cure_verdict_timed/2`."
  @spec idris_verdict_timed(String.t(), String.t(), timeout()) ::
          {:accept | :reject | :timeout, non_neg_integer()}
  def idris_verdict_timed(bin, idr_path, timeout \\ idris_timeout()),
    do: timed(timeout, fn -> idris_verdict(bin, idr_path) end)

  # Run `fun` in a task, bound by `timeout`; return `{result_or_:timeout, elapsed_ms}`.
  defp timed(timeout, fun) do
    start = System.monotonic_time(:millisecond)
    task = Task.async(fun)

    verdict =
      case Task.yield(task, timeout) || Task.shutdown(task, :brutal_kill) do
        {:ok, v} -> v
        _ -> :timeout
      end

    {verdict, System.monotonic_time(:millisecond) - start}
  end

  defp cure_timeout, do: env_int("ORACLE_CURE_TIMEOUT_MS", 120_000)
  defp idris_timeout, do: env_int("ORACLE_IDRIS_TIMEOUT_MS", 180_000)

  defp env_int(var, default) do
    case System.get_env(var) do
      nil -> default
      s -> String.to_integer(s)
    end
  end

  @doc """
  Idris' verdict via `idris2 --check`. The `.idr` is copied into a fresh
  throwaway directory and checked from there, so Idris' `build/` artifacts
  (which it writes into the current working directory) never pollute the repo.
  `IDRIS2_PATH` is set to the Prelude/base `.ttc` trees (see `idris_lib_path/1`)
  so `--check` resolves the standard library without a global `make install` —
  without this, every probe fails with "Module Prelude not found" and would
  false-`:reject`. An explicit `$IDRIS2_PATH` in the environment wins if set.
  """
  @spec idris_verdict(String.t(), String.t()) :: :accept | :reject
  def idris_verdict(bin, idr_path) do
    work = Path.join(System.tmp_dir!(), "cure_oracle_#{System.unique_integer([:positive])}")
    File.mkdir_p!(work)
    base = Path.basename(idr_path)
    File.cp!(idr_path, Path.join(work, base))

    env =
      case System.get_env("IDRIS2_PATH") || idris_lib_path(bin) do
        nil -> []
        path -> [{"IDRIS2_PATH", path}]
      end

    try do
      {out, status} =
        System.cmd(bin, ["--check", base], cd: work, env: env, stderr_to_stdout: true)

      # `idris2 --check` type-checks but does NOT hard-fail on totality: under
      # `%default total` a non-total / non-covering / non-positive definition is
      # reported as `Error: … is not total|not covering|not strictly positive`
      # yet the process still exits 0. For an ORACLE over PROOFS totality is
      # soundness (`foo : P; foo = foo` proves anything), so a type-check pass is
      # not enough — reject when Idris flags any totality violation, matching the
      # Cure side, which certifies totality before it will δ-reduce a proof.
      cond do
        status != 0 -> :reject
        Regex.match?(~r/is not total|is not covering|not strictly positive/, out) -> :reject
        true -> :accept
      end
    after
      File.rm_rf(work)
    end
  end

  # The Prelude/base `.ttc` search path derived from the idris2 binary's
  # location (`.../build/exec/idris2` → `.../libs/{prelude,base}/build/ttc`).
  # We `make bootstrap` the clone but never `make install`, so the stdlib lives
  # only in the build tree. Returns nil when those dirs are absent (e.g. a
  # system-installed idris2 that already knows its own Prelude path).
  @spec idris_lib_path(String.t()) :: String.t() | nil
  defp idris_lib_path(bin) do
    root = bin |> Path.dirname() |> Path.dirname() |> Path.dirname()
    prelude = Path.join([root, "libs", "prelude", "build", "ttc"])
    base = Path.join([root, "libs", "base", "build", "ttc"])

    if File.dir?(prelude) and File.dir?(base) do
      Enum.join([prelude, base], ":")
    else
      nil
    end
  end

  @doc "Default Idris binary: `$IDRIS2_BIN` or the pinned clone's build output."
  @spec default_idris_bin() :: String.t()
  def default_idris_bin do
    System.get_env("IDRIS2_BIN") ||
      Path.expand("~/Develop/Idris2/build/exec/idris2")
  end

  @doc "Read a cluster's committed fixture map (name => entry). Empty if absent."
  @spec read_fixture(String.t()) :: %{String.t() => map()}
  def read_fixture(cluster) do
    path = fixture_path(cluster)

    case File.read(path) do
      {:ok, body} -> JSON.decode!(body)
      {:error, _} -> %{}
    end
  end

  @doc "Write a cluster's fixture map as JSON."
  @spec write_fixture(String.t(), %{String.t() => map()}) :: :ok
  def write_fixture(cluster, fixture) do
    File.write!(fixture_path(cluster), JSON.encode!(fixture) <> "\n")
  end

  @doc "The relation contract. See moduledoc."
  @spec consistent(map()) :: :ok | {:error, term()}
  def consistent(%{"relation" => "same", "cure" => v, "idris" => v}), do: :ok

  def consistent(%{"relation" => rel, "idris" => "accept", "cure" => "reject", "reason" => reason})
      when rel in ["cure_stricter", "idris_only"] and is_binary(reason) and reason != "",
      do: :ok

  def consistent(entry), do: {:error, {:relation_violated, entry}}

  defp fixture_path(cluster), do: Path.join([@root, cluster, "verdicts.json"])
end
