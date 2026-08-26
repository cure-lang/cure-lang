defmodule Antigen.CoverageBaseline do
  @moduledoc """
  The **coverage-floor regression gate**. A committed per-module floor
  (`coverage_baseline.sexp`) records how many lines of each trusted kernel module
  a *pure, non-generative replay* of the committed corpora warms; the in-suite
  gate (`Antigen.CoverageBaselineTest`) re-measures and fails if any module drops
  below its floor.

  The measurement is a **replay**, not a campaign: it decodes the committed
  `corpus.sexp` + `seeds.sexp` + `reach.sexp` + `coverage.sexp` and re-runs each
  record's assay through the live kernel under `:cover`. No generators, no seeds,
  no sampling variance — so the gate is fast (~1s) and bit-stable, and a red gate
  always means a real coverage regression, never a flaky draw.

  `coverage.sexp` is the curated *coverage corpus*: the minimal set of challenges
  (beyond the pre-existing corpora) whose replay warms every reachable line. It is
  distilled greedily — keep a challenge iff its replay grows the covered-line set —
  from a deterministic generative pool, and is only ever (re)written by
  `mix antigen cover --record-new-coverage-baseline`. That command is the ONLY
  sanctioned way to move the floor: a genuine improvement raises it; newly-added
  proven-unreachable guard code (which lowers the ratio) is accepted by re-recording.
  Everyday `mix test` never regenerates it, so the floor cannot silently drift down.

  Residual cold lines under this replay (7, as of the value-surface batch) are the
  documented, proven-unreachable defensive backstops — guarded by a same-module
  invariant no public input can violate, so reaching them would need to call the
  private `defp` directly (which would weaken TCB encapsulation):

    * `Certificate` 471/478 — a mutual-SCC member always has a real body (a `nil`
      body yields no callees and is filtered out of the group), so `arity_of(nil)` /
      `function_edges(_,_,nil)` are unreachable; 603 — `shift_term`'s non-var/non-ctor
      catch-all, unreachable because `build_recon` only ever emits `{:ctor, _, [var…]}`.
    * `Inductive` 526 — `gather_data_heads`'s seen-cycle branch, shadowed by `occurs?`'s
      own cycle guard which short-circuits any global cycle before it is reached.
    * `Kernel` 1218 — `unify_spine`'s length-mismatch catch-all, guarded out by the
      equal-length lockstep of its callers; 1384/1390 — `replace_branch_var`'s self-map
      and depth-limit fallbacks, impossible under `bind_index`'s acyclic-forest invariant.
  """
  alias Antigen.{Cover, Runner, Corpus, CoverManifest, Generators}
  alias Antigen.Backend.StreamData, as: B

  @corpus "test/antigen/corpus.sexp"
  @seeds "test/antigen/seeds.sexp"
  @reach "test/antigen/reach.sexp"
  @coverage "test/antigen/coverage.sexp"
  @baseline "test/antigen/coverage_baseline.sexp"

  # Deterministic seed for the distillation's generative candidate pool. Only the
  # RECORD path draws generators; the gate never does. Fixed so re-recording on an
  # unchanged kernel reproduces the same corpus.
  @distill_seed 12_345
  @default_pool_count 4_000
  @kernel_probe_count 400
  @participant_count 200

  @doc "The committed corpora the gate replays, in order (pure replay, no generation)."
  @spec replay_paths() :: [String.t()]
  def replay_paths, do: [@corpus, @seeds, @reach, @coverage]

  @spec coverage_path() :: String.t()
  def coverage_path, do: @coverage

  @spec baseline_path() :: String.t()
  def baseline_path, do: @baseline

  # ── measurement (gate side): pure replay under :cover ──────────────────────

  @doc """
  Measure per-module coverage by replaying `paths` (default `replay_paths/0`)
  through the kernel under `:cover`. Returns `%{module => %{covered: n, total: n}}`.
  Deterministic: same committed files ⇒ same counts.
  """
  @spec measure([String.t()]) :: %{module() => %{covered: non_neg_integer(), total: non_neg_integer()}}
  def measure(paths \\ replay_paths()) do
    challenges = Enum.flat_map(paths, &records/1)

    Cover.with_cover(Cover.cover_modules(), fn ->
      Enum.each(challenges, &safe_replay/1)

      Map.new(Cover.cover_modules(), fn m ->
        c = Cover.line_coverage(m)
        {m, %{covered: length(c.covered), total: c.total}}
      end)
    end)
  end

  defp records(path),
    do:
      Corpus.stream(path)
      |> Enum.flat_map(fn
        {:ok, c} -> [c]
        _ -> []
      end)

  # A replay must never crash the gate: an ill-typed reconstructed record that the
  # live kernel rejects with a raise is not a coverage failure — it still warmed the
  # defensive line we care about. Swallow and continue.
  defp safe_replay(c) do
    Runner.replay_one(c)
  rescue
    _ -> :ok
  catch
    _, _ -> :ok
  end

  # ── floor file I/O ─────────────────────────────────────────────────────────

  @doc """
  Parse the committed floor file into `%{module => %{covered: n, total: n}}`.
  Returns `{:error, :missing}` if the file does not exist yet.
  """
  @spec read_baseline(String.t()) ::
          {:ok, %{module() => %{covered: non_neg_integer(), total: non_neg_integer()}}}
          | {:error, :missing}
  def read_baseline(path \\ @baseline) do
    if File.exists?(path) do
      floors =
        path
        |> File.stream!()
        |> Enum.flat_map(&parse_floor_line/1)
        |> Map.new()

      {:ok, floors}
    else
      {:error, :missing}
    end
  end

  @floor_re ~r/^\(cover-floor\s+(?<mod>\S+)\s+(?<cov>\d+)\s+(?<tot>\d+)\)/

  defp parse_floor_line(line) do
    case Regex.named_captures(@floor_re, String.trim(line)) do
      %{"mod" => mod, "cov" => cov, "tot" => tot} ->
        [{Module.concat([mod]), %{covered: String.to_integer(cov), total: String.to_integer(tot)}}]

      _ ->
        []
    end
  end

  @doc "Render + write the floor file from a `measure/1` result. One module per line."
  @spec write_baseline(%{module() => %{covered: non_neg_integer(), total: non_neg_integer()}}, String.t()) :: :ok
  def write_baseline(measured, path \\ @baseline) do
    rows =
      measured
      |> Enum.sort_by(fn {m, _} -> inspect(m) end)
      |> Enum.map(fn {m, %{covered: c, total: t}} ->
        "(cover-floor #{inspect(m)} #{c} #{t})"
      end)

    {tc, tt} =
      Enum.reduce(measured, {0, 0}, fn {_, %{covered: c, total: t}}, {ac, at} -> {ac + c, at + t} end)

    header = [
      "; Antigen kernel-coverage floor — per-module covered/total from a PURE REPLAY of",
      "; corpus.sexp + seeds.sexp + reach.sexp + coverage.sexp (no generation). A drop",
      "; below any floor fails test/antigen/coverage_baseline_test.exs. Regenerate ONLY via:",
      ";   mix antigen cover --record-new-coverage-baseline"
    ]

    body = header ++ rows ++ ["(cover-total #{tc} #{tt})"]
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, Enum.join(body, "\n") <> "\n")
  end

  # ── check ──────────────────────────────────────────────────────────────────

  @doc """
  Compare a `measure/1` result against a floor. Returns the list of regressions as
  `{module, floor_covered, current_covered}` (current is `nil` if the module vanished).
  Empty ⇒ no regression.
  """
  @spec regressions(map(), map()) :: [{module(), non_neg_integer(), non_neg_integer() | nil}]
  def regressions(measured, floor) do
    for {mod, %{covered: fcov}} <- floor,
        cur = measured[mod],
        cur == nil or cur.covered < fcov do
      {mod, fcov, cur && cur.covered}
    end
  end

  # ── distillation (record side): greedy minimal coverage corpus ─────────────

  @doc """
  Distil the coverage corpus: the minimal serializable challenges (beyond the
  pre-existing corpora) whose replay grows the covered-line set. Deterministic for
  a fixed kernel + `@distill_seed`.
  """
  @spec distill() :: [Antigen.Challenge.t()]
  def distill do
    committed = Enum.flat_map([@corpus, @seeds, @reach], &records/1)
    candidates = Enum.filter(committed ++ candidate_pool(), &serializable?/1)
    kept = greedy_keep(candidates)

    committed_keys = MapSet.new(committed, &Corpus.dedup_key(&1, :antibody))
    Enum.reject(kept, fn c -> MapSet.member?(committed_keys, Corpus.dedup_key(c, :antibody)) end)
  end

  @doc """
  Re-record the coverage corpus + floor. Rewrites `coverage.sexp` from a fresh
  distillation, then measures the pure replay and rewrites `coverage_baseline.sexp`.
  Returns `%{records: n, measured: measure_map}`.
  """
  @spec record!() :: %{records: non_neg_integer(), measured: map()}
  def record! do
    new = distill()

    File.rm_rf!(@coverage)

    # Bank with a per-record UNIQUE key (antibody key + index), NOT the plain
    # antibody key: scaffold-only kinds (`kernel/probe`, `decode_probe`) all share
    # one antibody key because the probe tag rides the scaffold, not the terms
    # list — so `Corpus.append`'s dedup would collapse all 20 probes to one record
    # and drop their coverage. The greedy pass already deduped by *coverage*, so
    # every record here is coverage-distinct; append still runs its portability
    # check (a non-portable record that would crash a fresh replay VM is dropped).
    banked =
      new
      |> Enum.with_index()
      |> Enum.count(fn {c, i} ->
        Corpus.append(@coverage, c, Corpus.dedup_key(c, :antibody) <> "##{i}") == :appended
      end)

    measured = measure()
    write_baseline(measured)
    %{records: banked, measured: measured}
  end

  # Deterministic generative candidate pool — the raw material the greedy pass
  # distils. Participants saturate their enumerable shape menus; KernelProbe is
  # drawn explicitly so all 20 probes (incl. the adversarial backstops) appear;
  # default_gen supplies broad term coverage.
  defp candidate_pool do
    part =
      CoverManifest.participants()
      |> Enum.flat_map(fn m ->
        try do
          B.sample_seeded(m.gen(), @participant_count, @distill_seed)
        rescue
          _ -> []
        catch
          _, _ -> []
        end
      end)

    B.sample_seeded(Generators.KernelProbe.gen(), @kernel_probe_count, @distill_seed) ++
      part ++
      B.sample_seeded(Mix.Tasks.Antigen.default_gen(), @default_pool_count, @distill_seed)
  end

  # A challenge is bankable iff it serializes (has a `to_pieces` clause and only
  # portable atoms) — the same gate `Corpus.append` enforces. Non-serializable
  # kinds can drive coverage in a live campaign but can't live in a replay corpus.
  defp serializable?(c) do
    _ = Corpus.dedup_key(c, :antibody)
    true
  rescue
    _ -> false
  catch
    _, _ -> false
  end

  defp greedy_keep(candidates) do
    Cover.with_cover(Cover.cover_modules(), fn ->
      {kept, _seen} =
        Enum.reduce(candidates, {[], Cover.covered_set(Cover.cover_modules())}, fn c, {keep, seen} ->
          safe_replay(c)
          now = Cover.covered_set(Cover.cover_modules())
          if MapSet.size(now) > MapSet.size(seen), do: {[c | keep], now}, else: {keep, seen}
        end)

      Enum.reverse(kept)
    end)
  end
end
