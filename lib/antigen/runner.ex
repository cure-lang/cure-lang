defmodule Antigen.Runner do
  @moduledoc "Explore / generate / replay orchestration (spec §8)."
  alias Antigen.{Backend, Corpus, Report, Challenge, Coverage}
  alias Cure.Core.Term

  # Health-gate floors (spec §8), scoped to the :typed_term subset for
  # binder-usage / reduction-activity; discard rate keeps its whole-run scope.
  @binder_usage_floor 0.60
  @reduction_activity_floor 0.25
  @discard_floor 0.10

  # Adaptive-biasing round size (spec §4). `default_gen`'s 11-branch mix maps to
  # three challenge-KIND groups; only Group T / Group M are ever reweighted.
  @round_size 200
  @group_table %{
    f: [1, 2, 3, 19, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35],
    t: [4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 29],
    m: [7, 8]
  }
  def gen_group_table, do: @group_table

  # Bump every position in the low-health group(s); floor 1; Group F never bumped.
  def reweight(weights, table \\ @group_table, stamps) do
    bumps =
      []
      |> maybe_bump(table.t, stamps[:health_stamp] == :vacuous or stamps[:conv_accept_count] == 0)
      |> maybe_bump(table.m, stamps[:mutation_stamp] == :vacuous or stamps[:conv_reject_count] == 0)

    weights
    |> Enum.with_index(1)
    |> Enum.map(fn {w, i} -> if i in bumps, do: w + 2, else: max(w, 1) end)
  end

  defp maybe_bump(acc, _positions, false), do: acc
  defp maybe_bump(acc, positions, true), do: acc ++ positions

  @doc """
  Coverage-guided reweighting (guided mode only): bump every generator position
  by its group's new-edge yield, so groups that discovered more new code get
  proportionally more draw weight next round. Floor 1 on every weight. Additive
  and opt-in — the default `explore`/`draw_biased` path uses `reweight/3` and is
  untouched. `edge_yields` is `%{group => new_edge_count}` (missing group ⇒ 0).
  """
  def reweight_by_edges(weights, table \\ @group_table, edge_yields) do
    bump_by_pos =
      Enum.reduce(table, %{}, fn {group, positions}, acc ->
        yield = Map.get(edge_yields, group, 0)
        Enum.reduce(positions, acc, fn pos, a -> Map.put(a, pos, yield) end)
      end)

    weights
    |> Enum.with_index(1)
    |> Enum.map(fn {w, i} -> max(w, 1) + Map.get(bump_by_pos, i, 0) end)
  end

  def explore(opts) do
    count = Keyword.get(opts, :count, 200)
    seed = Keyword.get(opts, :seed) || fresh_seed()

    challenges =
      cond do
        opts[:challenges] -> opts[:challenges]
        opts[:bias] -> draw_biased(opts[:gen], count, Keyword.get(opts, :round_size, @round_size), seed)
        # exactly one undivided draw when unbiased (spec §4 — take is not composable)
        true -> draw(opts[:gen], count, seed)
      end

    final =
      Enum.reduce(challenges, %{infections: 0, seeds_banked: 0, rejected: 0, discards: 0, coverage: MapSet.new()}, fn c,
                                                                                                                      acc ->
        run_challenge(c, opts, acc, count)
      end)

    metrics = health_metrics(challenges)
    discard_rate = final.discards / max(count, 1)
    stamp = health_stamp(metrics, discard_rate)

    IO.puts(
      "antigen health[typed_term]: binder_usage=#{Float.round(metrics.binder_usage, 2)} " <>
        "reduction_activity=#{Float.round(metrics.reduction_activity, 2)} " <>
        "fuel_exhausted=#{metrics.fuel_exhausted_count} discard=#{Float.round(discard_rate, 2)} → #{stamp}"
    )

    mm = mutation_metrics(challenges)

    if mm.mutants_total > 0 do
      IO.puts(
        "antigen health[mutant_term]: reason_diversity=#{mm.reason_diversity} " <>
          "max_depth=#{mm.max_depth} wrap_diversity=#{mm.wrap_diversity} " <>
          "survivors=#{mm.survivors} → #{mutation_stamp(mm)}"
      )
    end

    cm = conversion_metrics(challenges)

    if cm.conv_reject_count + cm.conv_accept_count > 0 do
      IO.puts(
        "antigen health[conversion]: carriers=#{cm.conv_carrier_diversity} " <>
          "both_polarities=#{cm.conv_both_polarities} " <>
          "reject=#{cm.conv_reject_count} accept=#{cm.conv_accept_count} → #{conversion_stamp(cm)}"
      )
    end

    %{
      infections: final.infections,
      seeds_banked: final.seeds_banked,
      rejected: final.rejected,
      seed: seed,
      health: summarize(final, count),
      health_metrics: metrics,
      stamp: stamp
    }
  end

  @doc """
  Health metrics over the :typed_term subset (spec §8): binder-usage and
  reduction-activity are scoped to :typed_term only; fuel-exhausted nf results
  are counted separately and excluded from reduction-activity.
  """
  def health_metrics(challenges) do
    tts = Enum.filter(challenges, &match?(%Challenge{kind: :typed_term}, &1))
    terms = Enum.map(tts, fn c -> c.payload.term end)

    {used, total} =
      Enum.reduce(terms, {0, 0}, fn t, {u, tot} ->
        {tu, tt} = binder_stats(t)
        {u + tu, tot + tt}
      end)

    {fired, denom, fuel_out} =
      Enum.reduce(tts, {0, 0, 0}, fn c, {f, d, fx} ->
        env = Antigen.Generators.SigMenu.env_of(c.payload.sig)
        ctx = Antigen.Generators.SigMenu.rebuild_context(env, c.payload.ctx)

        # `fuel: ...` matters here for the same reason it does in Assays.Term:
        # the 2-arg call defaults to :infinity, which would make
        # `fuel_exhausted_count` permanently 0 regardless of the corpus. Reuse
        # Assays.Term's committed constant rather than inventing a second one.
        case Cure.Core.Normalise.nf(ctx, c.payload.term, fuel: Antigen.Assays.Term.assay_fuel()) do
          :fuel_exhausted -> {f, d, fx + 1}
          nf -> {f + if(nf != c.payload.term, do: 1, else: 0), d + 1, fx}
        end
      end)

    %{
      binder_usage: safe_ratio(used, total),
      reduction_activity: safe_ratio(fired, denom),
      fuel_exhausted_count: fuel_out
    }
  end

  def health_stamp(metrics, discard_rate) do
    if metrics.binder_usage >= @binder_usage_floor and
         metrics.reduction_activity >= @reduction_activity_floor and
         discard_rate < @discard_floor,
       do: :healthy,
       else: :vacuous
  end

  @mutation_diversity_floor 5
  @depth_floor 4
  @wrap_floor 4

  @doc """
  Vacuity metrics over the :mutant_term subset: fault-kind diversity (spec §6.2),
  plus deep-propagation generation-quality signals `max_depth` / `wrap_diversity`.

  `reason_diversity` is scoped to correctly-REJECTED mutants; `max_depth` and
  `wrap_diversity` are generation-time properties computed over EVERY mutant
  (survivors included — excluding them would hide exactly the slice the gate needs).
  Legacy v1 seeds predate `:depth`/`:wrap_path`, so both are read defensively.
  """
  def mutation_metrics(challenges) do
    ms = Enum.filter(challenges, &match?(%Challenge{kind: :mutant_term}, &1))

    {rejected_kinds, survivors} =
      Enum.reduce(ms, {MapSet.new(), 0}, fn c, {kinds, surv} ->
        case Antigen.Assays.Mutation.run(c) do
          :ok -> {MapSet.put(kinds, c.payload.fault.kind), surv}
          {:violation, _} -> {kinds, surv + 1}
        end
      end)

    depths = Enum.map(ms, fn c -> Map.get(c.payload.fault, :depth, 0) end)
    wraps = ms |> Enum.flat_map(fn c -> Map.get(c.payload.fault, :wrap_path, []) end) |> MapSet.new()

    %{
      reason_diversity: MapSet.size(rejected_kinds),
      survivors: survivors,
      mutants_total: length(ms),
      max_depth: Enum.max([0 | depths]),
      wrap_diversity: MapSet.size(wraps)
    }
  end

  @doc """
  Vacuity stamp: diversity + depth + wrapper-diversity floors. Survivors are an
  infection, surfaced separately, never folded into the stamp (spec §6.2 rule).
  """
  def mutation_stamp(%{reason_diversity: d, max_depth: md, wrap_diversity: wd}),
    do:
      if(d >= @mutation_diversity_floor and md >= @depth_floor and wd >= @wrap_floor,
        do: :healthy,
        else: :vacuous
      )

  @conv_carrier_floor 2

  @doc """
  Structural carrier tag of a `:typed_term` conversion accept carrier, or nil.
  Accept challenges are ordinary `:typed_term`s (no fault field), so the conversion
  subset must be recognised by term shape. Safe in v1: the ordinary `Term` generator
  never emits a `plus`-headed Vec index (spec §6).
  """
  def conv_carrier_of(%Challenge{kind: :typed_term, payload: %{term: t}}) do
    case t do
      {:ctor, :vcons, [{:app, {:app, {:global, :plus}, _}, _}, _, _]} -> :conv_index
      {:case, _, {:lam, _g, _, {:data, :Vec, _, [{:app, {:app, {:global, :plus}, _}, _}]}}, _} -> :conv_motive
      _ -> nil
    end
  end

  def conv_carrier_of(_), do: nil

  @doc "Conversion-subset vacuity metrics over both polarities (spec §6)."
  def conversion_metrics(challenges) do
    rej =
      challenges
      |> Enum.filter(fn c ->
        match?(%Challenge{kind: :mutant_term}, c) and Map.get(c.payload.fault, :witness) == :conv
      end)
      |> Enum.map(fn c -> c.payload.fault.carrier end)

    acc = challenges |> Enum.map(&conv_carrier_of/1) |> Enum.reject(&is_nil/1)

    %{
      conv_carrier_diversity: MapSet.size(MapSet.new(rej ++ acc)),
      conv_both_polarities: rej != [] and acc != [],
      conv_reject_count: length(rej),
      conv_accept_count: length(acc)
    }
  end

  def conversion_stamp(%{conv_carrier_diversity: d, conv_both_polarities: both}),
    do: if(d >= @conv_carrier_floor and both, do: :healthy, else: :vacuous)

  # Count binders (lam / case-branch) and how many bind a variable that occurs.
  defp binder_stats(t), do: binder_stats(t, {0, 0})

  defp binder_stats({:lam, _g, _dom, body}, {u, tot}) do
    used = if occurs?(body, 0), do: 1, else: 0
    binder_stats(body, {u + used, tot + 1})
  end

  defp binder_stats({:case, scrut, _motive, branches}, acc) do
    # The motive is a type-level annotation the generator supplies (v1 uses a
    # constant motive whose binder is by construction unused), NOT a generated
    # term binder — spec §8's metric counts "lam / case-branch binders", so the
    # motive is deliberately excluded rather than dragging binder-usage down.
    acc = binder_stats(scrut, acc)

    Enum.reduce(branches, acc, fn {_c, arity, body}, {u, tot} ->
      used = if arity > 0 and Enum.any?(0..(arity - 1)//1, &occurs?(body, &1)), do: 1, else: 0
      tot2 = if arity > 0, do: tot + 1, else: tot
      binder_stats(body, {u + used, tot2})
    end)
  end

  defp binder_stats(t, acc) when is_tuple(t) do
    t |> Tuple.to_list() |> tl() |> Enum.reduce(acc, &binder_stats/2)
  end

  defp binder_stats(l, acc) when is_list(l), do: Enum.reduce(l, acc, &binder_stats/2)
  defp binder_stats(_leaf, acc), do: acc

  # Does de Bruijn index `k` occur free in `t`? (crosses binders by incrementing k)
  defp occurs?({:var, k}, k), do: true
  defp occurs?({:var, _}, _k), do: false
  defp occurs?({:lam, _g, dom, body}, k), do: occurs?(dom, k) or occurs?(body, k + 1)
  defp occurs?({:pi, _g, dom, cod}, k), do: occurs?(dom, k) or occurs?(cod, k + 1)

  defp occurs?({:case, scrut, motive, branches}, k) do
    # `motive` is itself a `:lam`-headed term (spec §6.5's constant-motive
    # convention); its extra binder lives inside its own `:lam` node and is
    # handled by the `:lam` clause, so motive stays at the SAME `k` here.
    occurs?(scrut, k) or occurs?(motive, k) or
      Enum.any?(branches, fn {_c, arity, body} -> occurs?(body, k + arity) end)
  end

  defp occurs?(t, k) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&occurs?(&1, k))
  defp occurs?(l, k) when is_list(l), do: Enum.any?(l, &occurs?(&1, k))
  defp occurs?(_leaf, _k), do: false

  defp safe_ratio(_num, 0), do: 1.0
  defp safe_ratio(num, den), do: num / den

  def generate(opts) do
    count = Keyword.get(opts, :count, 200)
    seed = Keyword.get(opts, :seed) || fresh_seed()

    draw(opts[:gen], count, seed)
    |> Enum.reduce(%{seeds_banked: 0, rejected: 0}, fn c, acc -> bank_seed(%{c | seed: seed_of(c)}, opts, acc) end)
    |> Map.take([:seeds_banked, :rejected])
    |> Map.put(:seed, seed)
  end

  def replay(paths, assays) do
    Enum.flat_map(paths, fn path ->
      Corpus.stream(path)
      |> Enum.map(fn
        {:ok, c} ->
          verdict =
            case Map.fetch(assays, c.assay) do
              {:ok, mod} -> apply(mod, :run, [c])
              :error -> {:violation, {:unknown_assay, c.assay}}
            end

          %{entry: c, verdict: verdict}

        {:decode_error, line, reason} ->
          %{entry: line, verdict: {:decode_error, line, reason}}
      end)
    end)
  end

  def replay_one(%Challenge{assay: a} = c), do: apply(assay_module(a), :run, [c])

  # Authoritative enumeration of every registered assay id (one per `assay_module/1`
  # clause below). Keep in sync with the dispatch — the runner_test asserts each
  # entry resolves to a module. The coverage-manifest gate uses this to detect a
  # registered-but-unwired assay (`Antigen.CoverManifest`).
  @registered_assays [
    "stub",
    "totality/diverging",
    "totality/terminating",
    "positivity",
    "reflexivity",
    "indexed/case",
    "rewrite/eq",
    "universes",
    "inductive/env_roundtrip",
    "term/rejection",
    "kernel/probe",
    "serialize/roundtrip",
    "serialize/decode",
    "conv/decision",
    "branchunify/verdict",
    "forcing/dot",
    "check/verdict",
    "delta/nf",
    "stuck_elim_delta",
    "term/infer_check",
    "term/subject_reduction",
    "term/normalization",
    "term/erasure_preservation",
    "mutation/rejection",
    "kernel/shift_subst",
    "kernel/weakening",
    "kernel/confluence",
    "kernel/beta_subst",
    "kernel/zeta_subst",
    "kernel/grade_conv",
    "kernel/effect_inert",
    "elab/shift_agrees",
    "elab/completeness",
    "elab/metamorphic",
    "elab/erasure",
    "elab/dot_forcing",
    "elab/guard_lint",
    "elab/nat_rep",
    "elab/soundness",
    "totality_closure/soundness",
    "totality_closure/completeness",
    "erasure/idempotent",
    "erasure/selective",
    "erasure/wellformed",
    "relevance/soundness"
  ]

  @doc "Every registered assay id (authoritative; keep in sync with `assay_module/1`)."
  @spec registered_assays() :: [String.t()]
  def registered_assays, do: @registered_assays

  # The assay registry: challenge assay-id → assay module.
  defp assay_module("stub"), do: Antigen.Assays.Stub
  defp assay_module("totality/diverging"), do: Antigen.Assays.Totality
  defp assay_module("totality/terminating"), do: Antigen.Assays.Totality
  defp assay_module("positivity"), do: Antigen.Assays.Positivity
  defp assay_module("reflexivity"), do: Antigen.Assays.Reflexivity
  defp assay_module("indexed/case"), do: Antigen.Assays.Indexed
  defp assay_module("rewrite/eq"), do: Antigen.Assays.Rewrite
  defp assay_module("universes"), do: Antigen.Assays.Universes
  defp assay_module("inductive/env_roundtrip"), do: Antigen.Assays.InductiveEnv
  defp assay_module("term/rejection"), do: Antigen.Assays.Malformed
  defp assay_module("kernel/probe"), do: Antigen.Assays.KernelProbe
  defp assay_module("serialize/roundtrip"), do: Antigen.Assays.Serialization
  defp assay_module("serialize/decode"), do: Antigen.Assays.Serialization
  defp assay_module("conv/decision"), do: Antigen.Assays.Conv
  defp assay_module("branchunify/verdict"), do: Antigen.Assays.BranchUnify
  defp assay_module("forcing/dot"), do: Antigen.Assays.DotForcing
  defp assay_module("check/verdict"), do: Antigen.Assays.CheckMode
  defp assay_module("delta/nf"), do: Antigen.Assays.DeltaReduce
  defp assay_module("stuck_elim_delta"), do: Antigen.Assays.StuckElimDelta
  defp assay_module("term/infer_check"), do: Antigen.Assays.Term
  defp assay_module("term/subject_reduction"), do: Antigen.Assays.Term
  defp assay_module("term/normalization"), do: Antigen.Assays.Term
  defp assay_module("term/erasure_preservation"), do: Antigen.Assays.Term
  defp assay_module("mutation/rejection"), do: Antigen.Assays.Mutation
  defp assay_module("kernel/shift_subst"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/weakening"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/confluence"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/beta_subst"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/zeta_subst"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/grade_conv"), do: Antigen.Assays.KernelLaw
  defp assay_module("kernel/effect_inert"), do: Antigen.Assays.KernelLaw
  defp assay_module("elab/shift_agrees"), do: Antigen.Assays.KernelLaw
  defp assay_module("elab/completeness"), do: Antigen.Assays.Elab
  defp assay_module("elab/metamorphic"), do: Antigen.Assays.Elab
  defp assay_module("elab/erasure"), do: Antigen.Assays.Elab
  defp assay_module("elab/dot_forcing"), do: Antigen.Assays.Elab
  defp assay_module("elab/guard_lint"), do: Antigen.Assays.Elab
  defp assay_module("elab/nat_rep"), do: Antigen.Assays.Elab
  defp assay_module("elab/soundness"), do: Antigen.Assays.Elab
  defp assay_module("totality_closure/soundness"), do: Antigen.Assays.TotalityClosureAssay
  defp assay_module("totality_closure/completeness"), do: Antigen.Assays.TotalityClosureAssay
  defp assay_module("erasure/idempotent"), do: Antigen.Assays.Erasure
  defp assay_module("erasure/selective"), do: Antigen.Assays.Erasure
  defp assay_module("erasure/wellformed"), do: Antigen.Assays.Erasure
  defp assay_module("relevance/soundness"), do: Antigen.Assays.Erasure

  @doc "Public view of the assay registry (for tests)."
  def assay_module_for(assay_id), do: assay_module(assay_id)

  @doc """
  The full assay replay registry: every registered assay id mapped to its module.
  Built from `registered_assays/0` + `assay_module_for/1`, so it stays in sync with
  the dispatch table automatically (unlike a hand-maintained literal). Consumers:
  `Antigen.Prune` (re-check each corpus record against the live kernel) and any
  replay driver that must cover *every* assay, not a hardcoded subset.
  """
  @spec replay_registry() :: %{String.t() => module()}
  def replay_registry do
    for id <- registered_assays(), into: %{}, do: {id, assay_module_for(id)}
  end

  defp bank_seed(c, opts, acc) do
    case Corpus.append(opts[:seeds_path], c, Corpus.dedup_key(c, :seed)) do
      :appended ->
        %{acc | seeds_banked: acc.seeds_banked + 1}

      :duplicate ->
        acc

      {:rejected, e} ->
        report_unportable(c, e)
        %{acc | rejected: acc.rejected + 1}
    end
  end

  # A record that reconstructs an atom absent from `Challenge.__known_atoms__/0`
  # would crash replay on a fresh VM. Keep this on stderr, but route it through
  # the same structured boundary as every other host-visible failure.
  defp report_unportable(c, e) do
    diagnostic =
      Cure.Diagnostic.Operational.artifact_error(
        "Antigen could not bank a non-portable record for assay `#{c.assay}` (kind `#{c.kind}`): " <>
          Exception.message(e),
        %{assay: c.assay, kind: c.kind, reason: Exception.message(e)}
      )

    Cure.Diagnostic.Host.emit_diagnostic(
      diagnostic,
      output_device: :standard_error,
      color: :auto,
      width: 80
    )
  end

  @doc """
  Process one challenge: bank its seed, run the assay, and on a violation
  minimize + write the infection report. Extracted verbatim from `explore/1`'s
  per-challenge reduce so the coverage-guided loop (`Antigen.Cover.guided_loop/1`)
  reuses the exact same dispatch.

  `opts[:health_extra]` (a 0-arg fun or a map; absent by default) is merged into
  the infection report's `health` map — the guided loop uses it to stamp the
  jackpot's coverage delta. The plain `explore` path passes nothing, merging
  `%{}`, so its behavior is byte-identical to before extraction.
  """
  def run_challenge(c, opts, acc, count) do
    c = %{c | seed: seed_of(c)}

    if well_formed?(c) do
      acc = %{acc | coverage: MapSet.union(acc.coverage, coverage_flags(c))}
      acc = bank_seed(c, opts, acc)

      case apply(opts[:assay] || assay_module(c.assay), :run, [c]) do
        :ok ->
          acc

        {:violation, orig_detail} = v ->
          assay = opts[:assay] || assay_module(c.assay)

          pred = fn ch ->
            case apply(assay, :run, [ch]) do
              {:violation, detail} -> same_shape?(detail, orig_detail)
              _ -> false
            end
          end

          {c_min, triage} = Antigen.Triage.minimize(c, pred, shrink_budget(opts))

          # A violation tagged `{:expected, _}` is a DELIBERATELY-injected one
          # (test scaffolding) — the immune system working, not a defect; render
          # it calmly so a normal test run's output does not read as a real bug.
          kind = if match?({:expected, _}, orig_detail), do: :immune_response, else: :infection

          health = summarize(acc, count) |> Map.put(:triage, triage) |> Map.merge(health_extra(opts))
          {:ok, path} = Report.write_infection(opts[:report_dir], c_min, v, health, kind)

          # A real infection is the whole point — print it, alarmingly. A
          # deliberately-injected immune response is expected scaffolding; tally it
          # (surfaced once at suite end) instead of flooding stdout per occurrence.
          case kind do
            :infection -> IO.puts(Report.breadcrumb(c_min, path, :infection))
            :immune_response -> Report.tally_immune_response()
          end

          case Corpus.append(opts[:corpus_path], c_min, Corpus.dedup_key(c_min, :antibody)) do
            {:rejected, e} -> report_unportable(c_min, e)
            _ -> :ok
          end

          %{acc | infections: acc.infections + 1}
      end
    else
      %{acc | discards: acc.discards + 1}
    end
  end

  defp health_extra(opts) do
    case opts[:health_extra] do
      nil -> %{}
      f when is_function(f, 0) -> f.()
      m when is_map(m) -> m
    end
  end

  @doc "Public single-batch draw (wraps the private `draw/3`) for the guided loop."
  def draw_n(gen, count), do: draw(gen, count, fresh_seed())

  # Seeded draw — every draw is replayable given `seed` (see `Backend.StreamData.sample_seeded/3`).
  defp draw(gen, count, seed), do: Backend.StreamData.sample_seeded(gen, count, seed)

  @doc """
  A fresh, wall-clock-derived master seed for an unseeded run. Distinct across
  `mix antigen` invocations (separate VMs) so each run prints a replayable seed.
  """
  @spec fresh_seed() :: integer()
  def fresh_seed, do: System.system_time(:microsecond)

  @doc """
  Per-round seed for a biased run, derived deterministically from the master `seed`
  and the 0-based round index. Keeps rounds independent (each its own RNG stream)
  yet fully reproducible from a single master seed.
  """
  @spec round_seed(integer(), non_neg_integer()) :: integer()
  def round_seed(seed, index), do: :erlang.phash2({seed, index})

  # `bias: true` draw (spec §4): draw `round_size` at a time, stamp the accumulated
  # batch's per-group health, reweight the mix, continue. Precondition: `gen` is the
  # reweightable `{:frequency, ws}` shape (`Mix.Tasks.Antigen.default_gen/0`) — an
  # ad-hoc non-frequency gen hits this match and crashes clearly rather than
  # silently misbehaving (bias:true is a CLI-only feature this run, §7 non-goals).
  defp draw_biased(gen, count, round_size, seed) do
    {:frequency, ws0} = gen
    # `round_size <= 0` would stall `draw_rounds/6` (n never decreases) — floor it,
    # since `opts[:round_size]` is caller-suppliable with no CLI validation.
    draw_rounds(ws0, count, max(round_size, 1), seed, 0, [])
  end

  defp draw_rounds(_ws, 0, _round_size, _seed, _idx, acc), do: acc |> Enum.reverse() |> List.flatten()

  defp draw_rounds(ws, remaining, round_size, seed, idx, acc) do
    n = min(round_size, remaining)
    # Each round draws from its own reproducible sub-seed derived from the master.
    batch = draw({:frequency, ws}, n, round_seed(seed, idx))
    stamps = round_stamps(List.flatten([batch | acc]))
    new_weights = reweight(Enum.map(ws, fn {w, _g} -> w end), gen_group_table(), stamps)
    ws2 = Enum.zip(new_weights, ws) |> Enum.map(fn {w, {_old_w, g}} -> {w, g} end)
    draw_rounds(ws2, remaining - n, round_size, seed, idx + 1, [batch | acc])
  end

  # `discard_rate` isn't knowable during the draw phase (discards are decided later,
  # in explore/1's reduce), so pass 0.0 — the mid-run bias stamp is driven by
  # binder_usage/reduction_activity; the run's real discard rate is still reported.
  defp round_stamps(challenges) do
    cm = conversion_metrics(challenges)

    %{
      health_stamp: health_stamp(health_metrics(challenges), 0.0),
      mutation_stamp: mutation_stamp(mutation_metrics(challenges)),
      conv_reject_count: cm.conv_reject_count,
      conv_accept_count: cm.conv_accept_count
    }
  end

  defp seed_of(c), do: c.seed || :erlang.phash2({c.kind, c.payload})

  @shrink_budget 2000
  defp shrink_budget(opts), do: opts[:shrink_budget] || @shrink_budget

  # compare only the violation TAG (leading atom of the detail tuple), never the
  # payload — which shrinks with the artifact. Fallback for non-tuple details
  # (e.g. Assays.Stub's bare :boom) avoids an elem/2 crash.
  defp same_shape?(d1, d2) when is_tuple(d1) and is_tuple(d2), do: elem(d1, 0) == elem(d2, 0)
  defp same_shape?(d1, d2), do: d1 == d2

  # Health gate (spec §9): discard rate (malformed candidates) + coverage buckets
  # (the binder-shape flags actually hit). Reported, never hard-failed.
  defp summarize(acc, count), do: %{discard_rate: acc.discards / max(count, 1), coverage: acc.coverage}

  defp coverage_flags(c) do
    {_ctors, _bucket, flags, _label} = Coverage.key(c)
    flags
  end

  # A generator-quality failure: a candidate whose Core terms aren't well-formed.
  # Distinct from a coverage-duplicate rejection (which is expected, not a discard).
  defp well_formed?(c) do
    c |> Coverage.terms_of() |> Enum.all?(&Term.term?/1)
  rescue
    _ -> false
  end
end
