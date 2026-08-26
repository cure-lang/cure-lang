defmodule Mix.Tasks.Antigen do
  @moduledoc """
  Run the Antigen property-based metatheory engine (spec §8).

      mix antigen [--count N | --budget Nm] [--bias] [--seed N] [--corpus PATH] [--seeds PATH] [--report-dir DIR]
      mix antigen generate [--count N | --budget Nm] [--seed N] [--seeds PATH] [--report-dir DIR]

  Every run prints the integer master seed it used (`seed=…`). Re-running with
  `--seed N` replays that run's generation exactly (deterministic draws, including
  each `--bias` round's sub-seed) — the way to reproduce a specific `mix antigen`
  run. `--seed` sets the RNG master seed; it is unrelated to `--seeds PATH` (the
  seed-corpus file).

  `mix antigen` is the **explorer**: generate → assay → bank; it self-terminates
  after a bounded number of generation rounds (`--count`, default #{20_000},
  a full run of ~30 seconds) or a wall-budget (`--budget 3m`, converted at a
  fixed `@rounds_per_minute`).

  `--bias` enables health-adaptive round-based generation (spec §4): the mix
  reweights toward the weakest vertical between rounds. It only has an observable
  effect when `--count` exceeds the 200 round size (otherwise the single round has
  no "next round" to reweight and it behaves like an unbiased run).

  `mix antigen generate` is **harvest-only**: it produces well-formed antigens,
  coverage-dedups, appends them to the seed store, and skips the assays entirely.

  ## Signals

  Every banked record is written with a single, atomic, synchronous append
  (`Antigen.Corpus.append/3`), so it is durable on disk the instant it lands.
  An untrapped **SIGINT** (Ctrl+C) therefore loses at most the in-flight record,
  never a previously-appended one. SIGINT is *not* application-interceptable and
  is deliberately **not** trapped here. A `:sigterm` handler is installed (outside
  the test env) only so an operator's `kill -TERM` prints a clean final line
  before the VM stops — it is not a durability mechanism.
  """
  use Mix.Task

  @shortdoc "Run the Antigen metatheory engine (explore | generate)"

  @default_count 20_000
  @rounds_per_minute 2000

  @switches [
    count: :integer,
    budget: :string,
    bias: :boolean,
    corpus: :string,
    seeds: :string,
    report_dir: :string,
    out: :string,
    guided: :boolean,
    precise: :boolean,
    edge_corpus: :string,
    plateau: :integer,
    guided_round: :integer,
    seed: :integer,
    record_new_coverage_baseline: :boolean
  ]

  @impl Mix.Task
  def run(argv) do
    {opts, rest, _} = OptionParser.parse(argv, strict: @switches)

    mode =
      cond do
        match?(["cover" | _], rest) -> :cover
        match?(["generate" | _], rest) -> :generate
        match?(["complete" | _], rest) -> :complete
        true -> :explore
      end

    count = resolve_count(opts)

    seeds_path = opts[:seeds] || "test/antigen/seeds.sexp"

    runner_opts = [
      # The three schema-directed generators; explore dispatches each challenge to
      # its assay via the runner's registry (no fixed `:assay` module).
      gen: default_gen(),
      corpus_path: opts[:corpus] || "test/antigen/corpus.sexp",
      seeds_path: seeds_path,
      report_dir: opts[:report_dir] || "tmp/antigen",
      count: count,
      bias: opts[:bias],
      # nil ⇒ the runner picks (and reports) a fresh seed; `--seed N` replays a run.
      seed: opts[:seed]
    ]

    # Install the corpus-backed filler pool (spec §3) once, before dispatch, so both
    # explore and generate share the pooled `gnat`. Inert if the seeds file is absent.
    Process.put(:antigen_seed_pool, Antigen.Generators.SeedPool.load(seeds_path))

    case mode do
      :explore ->
        r = Antigen.Runner.explore(runner_opts)

        IO.puts(
          "antigen: #{r.infections} infection(s), #{r.seeds_banked} seed(s) banked#{rejected_note(r)} (seed=#{r.seed})"
        )

      :generate ->
        install_sigterm_trap()
        r = Antigen.Runner.generate(runner_opts)
        IO.puts("antigen generate: #{r.seeds_banked} seed(s) banked#{rejected_note(r)} (seed=#{r.seed})")

        # Surface shape-coverage inline so a banking loop shows what the current
        # generators can/can't produce (same report `mix test` prints post-suite).
        case Antigen.CoverManifest.report(Antigen.CoverManifest.summary()) do
          nil -> :ok
          line -> IO.puts(line)
        end

      :complete ->
        run_complete(runner_opts)

      :cover ->
        if opts[:record_new_coverage_baseline] do
          record_coverage_baseline()
        else
          run_cover(opts, runner_opts)
        end
    end
  end

  @doc "Run deterministic shape coverage and corpus replay checks without banking data."
  def run_complete(opts) do
    summary = Antigen.CoverManifest.summary(800)

    replay_violations =
      if File.exists?(opts[:corpus_path]) do
        Antigen.Runner.replay([opts[:corpus_path]], Antigen.Runner.replay_registry())
        |> Enum.reject(&(&1.verdict == :ok))
      else
        []
      end

    cond do
      MapSet.size(summary.missing) > 0 ->
        Mix.raise("Antigen completion failed: uncovered shape cells #{inspect(Enum.sort(summary.missing))}")

      replay_violations != [] ->
        Mix.raise("Antigen completion failed: corpus replay violations #{inspect(replay_violations)}")

      true ->
        IO.puts("Antigen completion: #{summary.produced}/#{summary.expected} shape cells and corpus replay green")
    end
  end

  # Re-distil the coverage corpus + rewrite the floor. The ONLY sanctioned way to
  # move the coverage-baseline gate (`Antigen.CoverageBaselineTest`): a genuine
  # improvement raises the floor; newly-added proven-unreachable guard code is
  # accepted by re-recording. Everyday `mix test` never regenerates it.
  defp record_coverage_baseline do
    %{records: n, measured: m} = Antigen.CoverageBaseline.record!()
    {tc, tt} = Enum.reduce(m, {0, 0}, fn {_, v}, {a, b} -> {a + v.covered, b + v.total} end)

    IO.puts(
      "antigen cover --record-new-coverage-baseline: #{n} record(s) → " <>
        "#{Antigen.CoverageBaseline.coverage_path()}, floor #{tc}/#{tt} → " <>
        Antigen.CoverageBaseline.baseline_path()
    )
  end

  defp run_cover(opts, runner_opts) do
    {cover_mode, cover_opts} = cover_dispatch(opts, runner_opts)

    case cover_mode do
      :guided ->
        r = Antigen.Cover.guided_loop(cover_opts)

        IO.puts(
          "antigen cover --guided: #{r.covered_lines} kernel lines covered, " <>
            "#{r.banked} edge(s) banked, #{r.infections} infection(s) over #{r.rounds} round(s)"
        )

      :report ->
        {coverage, _report} = Antigen.Cover.run_report(cover_opts)
        covered = coverage |> Map.values() |> Enum.map(&length(&1.covered)) |> Enum.sum()
        total = coverage |> Map.values() |> Enum.map(& &1.total) |> Enum.sum()
        pct = if total > 0, do: Float.round(covered * 100 / total, 1), else: 0.0
        dest = if opts[:out], do: " → #{opts[:out]}", else: ""
        IO.puts("antigen cover: #{covered}/#{total} kernel lines (#{pct}%)#{dest}")
    end
  end

  @doc """
  Decide the `cover` sub-mode and build the opts passed to `Antigen.Cover`.
  `--guided` selects `:guided` (the coverage-guided loop); otherwise `:report`
  (the one-shot measurement). `--out`, `--edge-corpus`, and `--precise` are
  threaded onto the runner opts. Pure + public so the routing is unit-tested
  without running a campaign.
  """
  def cover_dispatch(opts, runner_opts) do
    merged =
      runner_opts
      |> Keyword.put(:out, opts[:out])
      |> Keyword.put(:edge_corpus, opts[:edge_corpus])
      |> Keyword.put(:precise, opts[:precise] || false)
      # only thread loop-tuning flags when present — an explicit nil would defeat
      # guided_loop's Keyword.get defaults
      |> maybe_put(:plateau, opts[:plateau])
      |> maybe_put(:guided_round, opts[:guided_round])

    mode = if opts[:guided], do: :guided, else: :report
    {mode, merged}
  end

  defp maybe_put(kw, _key, nil), do: kw
  defp maybe_put(kw, key, val), do: Keyword.put(kw, key, val)

  @doc "Convert a `\"Nm\"` wall-budget to a round count via the fixed `@rounds_per_minute`."
  @spec budget_to_count(String.t()) :: pos_integer()
  def budget_to_count(budget) do
    {minutes, _rest} = Integer.parse(budget)
    max(minutes, 1) * @rounds_per_minute
  end

  # Explorer default: Tier-A's three known-label generators + Tier-B's three
  # typed-term/assay-id branches + the mutation corpus + conversion-at-depth (both
  # polarities), weight 1 each. Public so tests can sample the wired distribution.
  def default_gen do
    Antigen.Gen.frequency([
      {1, Antigen.Generators.Totality.gen()},
      {1, Antigen.Generators.Positivity.gen()},
      {1, Antigen.Generators.Forcing.gen()},
      {1, Antigen.Generators.Term.typed_term("term/infer_check")},
      {1, Antigen.Generators.Term.typed_term("term/subject_reduction")},
      {1, Antigen.Generators.Term.typed_term("term/normalization")},
      {1, Antigen.Generators.Mutation.mutant()},
      {1, Antigen.Generators.Conversion.conv_reject()},
      {1, Antigen.Generators.Conversion.conv_accept("term/infer_check")},
      {1, Antigen.Generators.Conversion.conv_accept("term/subject_reduction")},
      {1, Antigen.Generators.Conversion.conv_accept("term/normalization")},
      {1, Antigen.Generators.Term.typed_term("kernel/shift_subst")},
      {1, Antigen.Generators.Term.typed_term("kernel/weakening")},
      {1, Antigen.Generators.Term.typed_term("kernel/confluence")},
      # Structure-directed primitive arithmetic — the reachability lever for
      # Eval.fold / Kernel.infer_prim / numeric_type? (the Int/Float paths the
      # mode-directed term generator never emits).
      {3, Antigen.Generators.Primitive.gen()},
      # Propositional-equality fragment — refl / Eq-type / rewrite; the lever for
      # the kernel's eq/refl/rewrite infer+eval+serialize+quote paths.
      {3, Antigen.Generators.Equality.gen()},
      # Type-formers (universes / Π / Σ / Vec types) — the lever for the kernel's
      # type-formation sort inference (infer_type_value_sort).
      {2, Antigen.Generators.TypeFormer.gen()},
      # Dependent matching — indexed Vec `case` with index refinement + dependent
      # motive; the lever for check_motive_wf/check_case_branches/unify_indices/
      # bind_index/specialize_branch_context/replace_branch_vars.
      {3, Antigen.Generators.DepMatch.gen()},
      # Indexed-family DECLARATION checking — the check_ctor → check_result_indices
      # path (result-index count/type validation); a family-shaped probe, group f.
      {2, Antigen.Generators.IndexedDecl.gen()},
      # Malformed terms (NEGATIVE vertical) — the kernel must REJECT; the lever for
      # infer's defensive rejection clauses (absurd/unknown_global/family/ctor,
      # case-scrutinee-not-data, ensure_pi/ensure_eq guards).
      {2, Antigen.Generators.Malformed.gen()},
      # Serialization roundtrip (metamorphic) — decode ∘ encode = id over every
      # serialisable shape; the lever for Serialize's DECODE path (tokenize/parse/
      # build/build_node) which the banking-only campaign never replays.
      {2, Antigen.Generators.Serialization.gen()},
      # Serialization decode robustness — raw S-expr strings straight to decode;
      # the lever for the bare-leaf / string / parse-error decode edges.
      {2, Antigen.Generators.DecodeProbe.gen()},
      # Conversion decision — term pairs with a known convertibility verdict over a
      # neutral context; the lever for Conv's stuck-neutral / η / no-δ clauses.
      {2, Antigen.Generators.ConvPair.gen()},
      # Branch unification — direct branch_unify/4 calls with known verdicts; the
      # lever for the kernel's index unifier (unify_one/bind_index/unify_spine/
      # rigid_index?/head_key) past what a well-typed case reaches.
      {2, Antigen.Generators.BranchUnify.gen()},
      # Dot-forcing (#24) — forced/dot-pattern soundness: {name=.e} check-and-discard
      # annotation; the lever for the elaborator's named-implicit forced-value
      # resolution + the :unforced gate + Conv.conv? accept/reject decision.
      {2, Antigen.Generators.DotForcing.gen()},
      # Check-mode — direct Kernel.check/3 verdicts; the lever for checking-mode-only
      # forms (parameter-bearing ctors, holes, Σ-introduction) inference can't reach.
      {2, Antigen.Generators.CheckMode.gen()},
      # Delta-reduction — δ-unfolding of certified globals under Normalise.nf; the
      # only lever for unfold_certified_head + its ι-follow-through (definitional eq).
      {2, Antigen.Generators.DeltaReduce.gen()},
      # Capture-avoiding β (kernel/beta_subst) — redexes with capture traps; the
      # kernel-level proof that β agrees with the elaborator's shifting substitution
      # (validates the bind-once β-redex the guard/let elaboration emits, #4/#26).
      {2, Antigen.Generators.BetaSubst.gen()},
      # Elaborator/kernel shift agreement — over generated meta-free terms, the
      # elaborator's Subst.shift must equal the kernel's Term.shift (the shift-half
      # of the beta_subst cross-check; a TCB-boundary capture guard).
      {1, Antigen.Generators.Term.typed_term("elab/shift_agrees")},
      # Inductive Env-accessor roundtrip — declares straight through
      # `Inductive.declare/3`/`register_builtin/3` and reads the family/ctor
      # metadata back through the accessor layer (`family?`, `arg_telescope`,
      # `ctor_result_indices`, `field_count`, `ctor_quantities`,
      # `index_telescope`, `param_telescope`, `ctor_result_params`); the lever
      # for the Env-accessor cold-line bucket every other family-shaped
      # generator bypasses by never reading a declaration back out.
      {1, Antigen.Generators.InductiveEnv.gen()},
      # Elaborator-driven literal typing (compact-Nat coverage batch) — the lever
      # for Kernel.bool_type_value/1 (boolean literal, inference position) and
      # Kernel.nat_type_value/1 (Nat-checked literal, re-checked via elab/soundness
      # over the real prelude env) — neither reachable from a bare Core-term probe.
      {1, Antigen.Generators.ElabLiteralTyping.gen()},
      # Kernel def-level probes (cold-line completion batch) — the lever for the
      # check_def / validate_certificate / check_family / normalize-3 / Final-Core
      # validator-emit / infer-rejection / remap_index_error defensive clauses that
      # are entry points into the kernel's def and family machinery, not `infer` of
      # a single closed term, so no term-shaped generator reaches them.
      {1, Antigen.Generators.KernelProbe.gen()},

      # 33. ζ for the Core `:let` binder — the same capture traps as `BetaSubst`
      # (position 28), so a divergence between the two is attributable to the
      # `:let` node alone. APPENDED, not inserted next to its sibling: the group
      # table in `Antigen.Runner` is indexed by POSITION, so inserting mid-list
      # silently renumbers every generator after it and adaptive reweighting then
      # bumps the wrong ones. Group `f` (fixed menu).
      {2, Antigen.Generators.ZetaSubst.gen()},

      # 34. A binder's GRADE is part of type identity (Idris Convert.idr:328).
      # APPENDED, like ZetaSubst: `@group_table` is indexed by POSITION.
      {2, Antigen.Generators.GradeConv.gen()},

      # 35. `Effect` inertness invariance — the inert `Effect`/`pure`/`bind`
      # signature must NEVER reduce (no monad laws): `nf` preserves the effect
      # skeleton and `bind(pure(a), k) ≢ k(a)`. APPENDED, like GradeConv: the
      # `@group_table` is indexed by POSITION, so a mid-list insert renumbers
      # every generator after it and adaptive reweighting bumps the wrong ones.
      # Group `f` (fixed menu).
      {2, Antigen.Generators.EffectInert.gen()}
    ])
  end

  # Tally note for records the portability guard refused to bank (each was already
  # reported loudly to stderr as it happened — see `Runner.report_unportable/2`).
  defp rejected_note(%{rejected: n}) when is_integer(n) and n > 0,
    do: ", #{n} non-portable rejected"

  defp rejected_note(_), do: ""

  defp resolve_count(opts) do
    cond do
      opts[:count] -> opts[:count]
      opts[:budget] -> budget_to_count(opts[:budget])
      true -> @default_count
    end
  end

  # Trap SIGTERM only, and never during `mix test` (a lingering handler would
  # outlive the test). SIGINT is intentionally left untrapped — see moduledoc.
  defp install_sigterm_trap do
    if Mix.env() != :test do
      try do
        System.trap_signal(:sigterm, fn ->
          IO.puts("antigen: SIGTERM — every banked record is already durable; stopping.")
          System.halt(0)
        end)
      rescue
        _ -> :ok
      end
    end

    :ok
  end
end
