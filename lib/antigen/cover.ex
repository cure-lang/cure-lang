defmodule Antigen.Cover do
  @moduledoc "Erlang :cover harness for kernel code coverage (Antigen tooling; no TCB changes)."

  @cover_modules [
    Cure.Core.Kernel,
    Cure.Core.Normalise,
    Cure.Core.Conv,
    Cure.Core.Eval,
    Cure.Core.Quote,
    Cure.Core.Inductive,
    Cure.Core.Serialize,
    Cure.Core.Certificate
  ]
  def cover_modules, do: @cover_modules

  @doc """
  True if `module`'s beam carries real abstract_code (required by both
  :cover.compile_beam AND Task 3's function_index; :cover.analyse needs the
  former, cold-line→function mapping needs the latter — same underlying chunk).

  MUST inspect the chunk's inner VALUE, not just that :beam_lib.chunks/2
  returned :ok — confirmed against OTP: :beam_lib.chunks(beam, [:abstract_code])
  ALWAYS returns {:ok, {Mod, [...]}} for any valid .beam, even when abstract
  code is absent; absence is signalled by the sentinel atom
  `:no_abstract_code` as the chunk's VALUE, not by an outer :error. A guard
  that only pattern-matches the outer {:ok, _} is vacuously always true and
  never rejects anything — the negative test exists specifically to catch that.
  """
  def cover_compilable?(module) do
    case :code.which(module) do
      beam when is_list(beam) ->
        match?(
          {:ok, {^module, [{:abstract_code, {:raw_abstract_v1, _forms}}]}},
          :beam_lib.chunks(beam, [:abstract_code])
        )

      _ ->
        false
    end
  end

  @doc "Run `fun` with `modules` cover-compiled; always :cover.stop afterward."
  def with_cover(modules, fun) do
    # :cover.start/0 returns {:ok, pid} the first time and
    # {:error, {:already_started, pid}} if a cover session already exists on the
    # node — both mean "the cover server is available"; only a genuinely
    # different error should surface.
    case :cover.start() do
      {:ok, _} -> :ok
      {:error, {:already_started, _}} -> :ok
    end

    try do
      Enum.each(modules, fn m ->
        {:ok, ^m} = normalize_compile({:cover.compile_beam(m), m}, m)
      end)

      fun.()
    after
      :cover.stop()
    end
  end

  defp normalize_compile({{:ok, m}, _}, m), do: {:ok, m}

  defp normalize_compile({{:error, reason}, m}, m),
    do: raise("cover.compile_beam failed for #{inspect(m)}: #{inspect(reason)}")

  @doc """
  Line-level coverage for a cover-compiled `module`. MUST be called inside a
  `with_cover/2` block (before `:cover.stop`). Returns
  `%{covered: [line], cold: [line], total: n}`, excluding the `{{Mod, 0}, {0, 1}}`
  module-level pseudo-entry that `:cover.analyse` always emits.
  """
  def line_coverage(module) do
    {:ok, pairs} = :cover.analyse(module, :coverage, :line)

    {cov, cold} =
      pairs
      |> Enum.reject(fn {{_m, line}, _} -> line == 0 end)
      |> Enum.reduce({[], []}, fn {{_m, line}, {c, _n}}, {yes, no} ->
        if c > 0, do: {[line | yes], no}, else: {yes, [line | no]}
      end)

    %{covered: Enum.sort(cov), cold: Enum.sort(cold), total: length(cov) + length(cold)}
  end

  @doc """
  Runs an Antigen campaign (`Runner.explore/1` with `opts`) with all
  `@cover_modules` cover-compiled, then returns `{coverage_map, report}` where
  `coverage_map` is `%{module => line_coverage/1}` and `report` is the rendered
  markdown (also written to `opts[:out]` if given). The campaign runs inside
  `with_cover/2`, so instrumentation is always torn down afterward.
  """
  def run_report(opts) do
    coverage =
      with_cover(@cover_modules, fn ->
        _ = Antigen.Runner.explore(opts)
        Map.new(@cover_modules, fn m -> {m, line_coverage(m)} end)
      end)

    fn_indexes = Map.new(@cover_modules, fn m -> {m, Antigen.CoverReport.function_index(m)} end)
    report = Antigen.CoverReport.render(coverage, fn_indexes)
    if out = opts[:out], do: File.write!(out, report)
    {coverage, report}
  end

  # -- Phase 2: coverage-guided feedback --------------------------------------

  @doc """
  The set of currently-covered `{module, line}` pairs across `modules`, read
  from live cover state. MUST be called inside a `with_cover/2` block. Cover
  accumulates, so this set grows monotonically until `:cover.reset/0`.
  """
  def covered_set(modules) do
    Enum.reduce(modules, MapSet.new(), fn m, acc ->
      Enum.reduce(line_coverage(m).covered, acc, fn line, a -> MapSet.put(a, {m, line}) end)
    end)
  end

  @doc """
  Batch-gate: `{module, line}` pairs covered now but not in `prev_set`. One
  `:cover.analyse` per module — cheap enough to run every round to decide
  whether a round is interesting before paying for precise attribution.
  """
  def delta(prev_set, modules) do
    MapSet.difference(covered_set(modules), prev_set)
  end

  @doc """
  Precise re-attribution: for each challenge, `:cover.reset/0` then `run_fun.(ch)`
  and measure the `{module, line}` pairs it covers beyond `prev_set`. Returns
  `[{challenge, novel_set}]`.

  `:cover.reset/0` clears counters node-wide, so this is only valid inside a
  `with_cover/2` block and destroys the accumulated coverage — the caller must
  re-establish its baseline afterward. Reserve it for rounds the batch-gate
  already flagged as interesting.
  """
  def attribute(prev_set, challenges, run_fun, modules) do
    Enum.map(challenges, fn ch ->
      :cover.reset()
      run_fun.(ch)
      {ch, MapSet.difference(covered_set(modules), prev_set)}
    end)
  end

  @edge_shrink_budget 200

  @doc """
  Bank an interesting `challenge` (one that hit `new_lines`) into the edge corpus
  at `edge_corpus_path`, keyed for dedup by its covered-line set.

  Two dedup layers: the in-memory `seen_sets` MapSet gates on the covered-line
  set (`MapSet.new(new_lines)`) so a second input with identical new coverage is
  skipped before any work; `Corpus.append/3` then dedups on disk by the
  `:antibody` content key (matching `Runner.explore`). Before banking, the
  challenge is `Triage.minimize/3`-shrunk under `pred` — the guided loop supplies
  a predicate that re-runs the challenge under cover and checks it still hits ≥1
  of `new_lines`; the shrink keeps the smallest input that preserves the edge.

  Returns `{status, banked_challenge | nil, updated_seen_sets}` where `status` is
  `:appended | :duplicate | :skipped`.
  """
  def bank_interesting(challenge, new_lines, edge_corpus_path, seen_sets, pred, budget \\ @edge_shrink_budget) do
    key = MapSet.new(new_lines)

    if MapSet.member?(seen_sets, key) do
      {:skipped, nil, seen_sets}
    else
      {c_min, _stats} = Antigen.Triage.minimize(challenge, pred, budget)
      status = Antigen.Corpus.append(edge_corpus_path, c_min, Antigen.Corpus.dedup_key(c_min, :antibody))
      {status, c_min, MapSet.put(seen_sets, key)}
    end
  end

  @doc """
  Merge the edge corpus's seeds into the live `:antigen_seed_pool` process-dict
  entry so `Mutation.gnat`'s crossover can draw banked interesting inputs within
  the same run (the pool is otherwise loaded once at startup). Merges rather than
  replaces, preserving the startup seed pool.

  Only closed `:typed_term` bankings with `ctx: []` reach the pool —
  `SeedPool.load/1` drops every other challenge kind by design; for those, the
  interesting input is still durably banked to the edge corpus (Task 7), it just
  does not feed crossover. Returns the merged pool.
  """
  def refresh_seed_pool!(edge_corpus_path) do
    edge_pool = Antigen.Generators.SeedPool.load(edge_corpus_path)

    merged =
      Map.merge(Process.get(:antigen_seed_pool, %{}), edge_pool, fn _type, a, b ->
        Enum.uniq(a ++ b)
      end)

    Process.put(:antigen_seed_pool, merged)
    merged
  end

  @guided_round 50
  @guided_plateau 2
  @default_edge_corpus "test/antigen/edge_corpus.sexp"

  @doc """
  Coverage-guided fuzzing loop. Draws challenges in rounds with the kernel
  cover-compiled; after each challenge measures its new-line coverage delta and,
  when it hit new lines, banks it to the edge corpus (Task 7), live-refreshes the
  seed pool so crossover can reuse it (Task 8), and credits its generator group's
  edge yield. At each round boundary the generator is reweighted toward the
  highest-yield groups (Task 9). Terminates when `plateau` consecutive rounds add
  no new edge, or the `count` budget is spent.

  Jackpots (a challenge that both hits a new edge and violates) produce a SINGLE
  infection report whose `health` map carries a `:coverage_delta` field, threaded
  through `Runner.run_challenge`'s `:health_extra` hook — never a second report.

  Coverage is attributed per-challenge (precise). Banked inputs are stored as-is
  (`budget: 0`): coverage-exact shrink would need `:cover.reset`, which destroys
  the loop's accumulated baseline, so it is deferred to an offline edge-corpus
  post-pass. Returns a summary map.
  """
  def guided_loop(opts) do
    modules = cover_modules()
    edge_path = opts[:edge_corpus] || @default_edge_corpus
    count = Keyword.get(opts, :count, 200)
    round_size = Keyword.get(opts, :guided_round, @guided_round)
    plateau_limit = Keyword.get(opts, :plateau, @guided_plateau)

    # line_coverage/1 must run INSIDE with_cover (live cover state); function_index/1
    # must run OUTSIDE (it reads the real .beam via :code.which, which returns the
    # `cover_compiled.beam` sentinel while a module is instrumented). Split exactly
    # as run_report/1 does: harvest coverage inside, render + write after teardown.
    {summary, coverage} =
      with_cover(modules, fn ->
        init = %{
          acc: %{infections: 0, seeds_banked: 0, discards: 0, coverage: MapSet.new()},
          covered: covered_set(modules),
          seen_sets: MapSet.new(),
          gen: opts[:gen],
          rounds: 0,
          plateau: 0,
          banked: 0
        }

        st = guided_rounds(opts, modules, edge_path, count, round_size, plateau_limit, init)

        cov = if opts[:out], do: Map.new(modules, fn m -> {m, line_coverage(m)} end), else: nil

        {%{
           infections: st.acc.infections,
           rounds: st.rounds,
           banked: st.banked,
           covered_lines: MapSet.size(st.covered)
         }, cov}
      end)

    if coverage do
      fn_indexes = Map.new(modules, fn m -> {m, Antigen.CoverReport.function_index(m)} end)
      File.write!(opts[:out], Antigen.CoverReport.render(coverage, fn_indexes))
    end

    summary
  end

  defp guided_rounds(opts, modules, edge_path, count, round_size, plateau_limit, st) do
    cond do
      st.plateau >= plateau_limit ->
        st

      st.rounds * round_size >= count ->
        st

      true ->
        round_start = st.covered
        challenges = Antigen.Runner.draw_n(st.gen, round_size)

        {st2, yields} =
          if opts[:precise],
            do: run_round_precise(challenges, opts, modules, edge_path, count, st),
            else: run_round_batch(challenges, opts, modules, edge_path, count, st)

        round_new = MapSet.difference(st2.covered, round_start)
        plateau = if MapSet.size(round_new) == 0, do: st.plateau + 1, else: 0

        guided_rounds(opts, modules, edge_path, count, round_size, plateau_limit, %{
          st2
          | gen: reweight_gen(st2.gen, yields),
            rounds: st.rounds + 1,
            plateau: plateau
        })
    end
  end

  # Precise: measure coverage after EVERY challenge, attribute + bank per input.
  # Accurate per-input deltas at the cost of one analyse-set per challenge.
  defp run_round_precise(challenges, opts, modules, edge_path, count, st) do
    Enum.reduce(challenges, {st, %{f: 0, t: 0, m: 0}}, fn c, {s, ys} ->
      prev = s.covered

      opts_c =
        Keyword.put(opts, :health_extra, fn ->
          %{coverage_delta: MapSet.size(MapSet.difference(covered_set(modules), prev))}
        end)

      acc2 = Antigen.Runner.run_challenge(c, opts_c, s.acc, count)
      new_lines = MapSet.difference(covered_set(modules), prev)
      s = %{s | acc: acc2, covered: MapSet.union(prev, new_lines)}

      if MapSet.size(new_lines) > 0 do
        {_status, _min, seen2} =
          bank_interesting(c, new_lines, edge_path, s.seen_sets, fn _ -> true end, 0)

        refresh_seed_pool!(edge_path)
        grp = challenge_group(c)
        n = MapSet.size(new_lines)
        {%{s | seen_sets: seen2, banked: s.banked + 1}, Map.update(ys, grp, n, &(&1 + n))}
      else
        {s, ys}
      end
    end)
  end

  # Batch (default): measure coverage only at round boundaries — one analyse-set
  # per round instead of per challenge (the cheap gate; spec Risk #2). Banks one
  # representative per interesting round (seen_sets dedups on the round's new-line
  # set). Jackpot coverage_delta is round-level. No :cover.reset — the round delta
  # is an accumulating-set difference, so the loop's baseline is never destroyed.
  defp run_round_batch(challenges, opts, modules, edge_path, count, st) do
    round_prev = st.covered

    opts_r =
      Keyword.put(opts, :health_extra, fn ->
        %{coverage_delta: MapSet.size(MapSet.difference(covered_set(modules), round_prev))}
      end)

    acc2 =
      Enum.reduce(challenges, st.acc, fn c, acc ->
        Antigen.Runner.run_challenge(c, opts_r, acc, count)
      end)

    round_new = MapSet.difference(covered_set(modules), round_prev)
    s = %{st | acc: acc2, covered: MapSet.union(round_prev, round_new)}

    if MapSet.size(round_new) > 0 do
      Enum.reduce(challenges, {s, %{f: 0, t: 0, m: 0}}, fn c, {ss, ys} ->
        {status, _min, seen2} =
          bank_interesting(c, round_new, edge_path, ss.seen_sets, fn _ -> true end, 0)

        ss = %{ss | seen_sets: seen2}

        if status == :appended do
          refresh_seed_pool!(edge_path)
          grp = challenge_group(c)
          n = MapSet.size(round_new)
          {%{ss | banked: ss.banked + 1}, Map.update(ys, grp, n, &(&1 + n))}
        else
          {ss, ys}
        end
      end)
    else
      {s, %{f: 0, t: 0, m: 0}}
    end
  end

  # Map a challenge to its generator group (parallels Runner's @group_table).
  defp challenge_group(%{kind: :mutant_term}), do: :m
  defp challenge_group(%{kind: :typed_term}), do: :t
  defp challenge_group(_), do: :f

  # Rebuild a reweightable {:frequency, ws} generator biased by per-group edge
  # yield; any other generator shape is drawn unchanged (parallels draw_biased).
  defp reweight_gen({:frequency, ws}, yields) do
    weights = Enum.map(ws, fn {w, _g} -> w end)
    gens = Enum.map(ws, fn {_w, g} -> g end)
    new_weights = Antigen.Runner.reweight_by_edges(weights, Antigen.Runner.gen_group_table(), yields)
    {:frequency, Enum.zip(new_weights, gens)}
  end

  defp reweight_gen(gen, _yields), do: gen
end
