defmodule Antigen.CoverGuidedTest.CoverThenViolate do
  @moduledoc false
  # Runs the challenge's REAL assay first (so the cover-compiled kernel actually
  # executes and coverage accumulates), then forces a violation so the guided
  # loop always has a jackpot to report. A pure {:violation} stub would never
  # touch the kernel and thus never generate coverage. The violation is tagged
  # `{:expected, _}` so the Runner renders it as a (calm) immune response rather
  # than an alarming "ANTIGEN INFECTION" — it is deliberate scaffolding.
  def run(%Antigen.Challenge{assay: assay} = c) do
    _ =
      try do
        apply(Antigen.Runner.assay_module_for(assay), :run, [c])
      rescue
        _ -> :ok
      catch
        _, _ -> :ok
      end

    {:violation, {:expected, :forced}}
  end
end

defmodule Antigen.CoverGuidedTest do
  # :cover (+ :cover.reset) is node-wide global
  use ExUnit.Case, async: false
  alias Antigen.{Cover, Triage, Challenge, Corpus}

  @nat {:data, :Nat, [], []}
  defp d(name, body), do: %{name: name, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}

  # Reducible in both dimensions: droppable defs (g, h) + an S-tower body to shrink.
  defp both_dims_ch do
    tower = {:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}]}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [d(:f, tower), d(:g, {:ctor, :Z, []}), d(:h, {:ctor, :Z, []})], focus: [:f]},
      seed: 1
    )
  end

  test "delta/2 reports newly-covered lines and is empty when nothing new is hit" do
    Cover.with_cover([Antigen.CoverFixture], fn ->
      # hit the :pos branch
      Antigen.CoverFixture.classify(5)
      s1 = Cover.covered_set([Antigen.CoverFixture])

      # hit :neg — a NEW line
      Antigen.CoverFixture.classify(-1)
      d1 = Cover.delta(s1, [Antigen.CoverFixture])
      assert MapSet.size(d1) > 0
      assert Enum.all?(d1, fn {m, l} -> m == Antigen.CoverFixture and is_integer(l) end)

      s2 = Cover.covered_set([Antigen.CoverFixture])
      # hit :neg again — nothing new
      Antigen.CoverFixture.classify(-2)
      d2 = Cover.delta(s2, [Antigen.CoverFixture])
      assert MapSet.size(d2) == 0
    end)
  end

  test "attribute/4 pins each challenge's novel coverage via per-challenge reset" do
    # Cover's cond line-attribution (confirmed by probe): classify(0) covers the
    # `n<0 -> :neg` head line 4 and the `n==0` guard line 6; classify(-1) covers
    # the :neg body line 5; classify(5) covers line 6 + the `true -> :pos` line 7.
    # So with a classify(0) baseline, -1 introduces line 5 and 5 introduces line 7 —
    # two distinct, non-empty novel sets. (A classify(5) baseline would make
    # classify(0) contribute nothing novel, since line 6 is already covered — a
    # correct result that just doesn't exercise the "distinct novel" assertion.)
    Cover.with_cover([Antigen.CoverFixture], fn ->
      # baseline: lines {4, 6}
      Antigen.CoverFixture.classify(0)
      prev = Cover.covered_set([Antigen.CoverFixture])

      run = fn n -> Antigen.CoverFixture.classify(n) end
      attributed = Cover.attribute(prev, [-1, 5], run, [Antigen.CoverFixture])

      assert length(attributed) == 2
      assert Enum.all?(attributed, fn {_ch, novel} -> MapSet.size(novel) > 0 end)
      [{-1, neg_novel}, {5, pos_novel}] = attributed
      refute MapSet.equal?(neg_novel, pos_novel)
    end)
  end

  test "bank_interesting minimizes, banks to the edge corpus, and dedups by covered-line set" do
    ch = both_dims_ch()
    path = Path.join(System.tmp_dir!(), "edge_#{System.unique_integer([:positive])}.sexp")
    on_exit(fn -> File.rm_rf!(path) end)

    lines = MapSet.new([{Cure.Core.Eval, 107}, {Cure.Core.Eval, 108}])
    # always interesting → Triage shrinks maximally
    pred = fn _c -> true end

    {status1, banked, seen1} = Cover.bank_interesting(ch, lines, path, MapSet.new(), pred, 500)
    assert status1 == :appended
    # actually minimized
    assert Triage.size(banked) < Triage.size(ch)
    assert Enum.count(Corpus.stream(path)) == 1

    # a second, different challenge carrying the SAME covered-line set is NOT
    # re-banked — the in-memory seen_sets gate (not the on-disk key) enforces this.
    ch2 = %{ch | seed: 2}
    {status2, _b2, _seen2} = Cover.bank_interesting(ch2, lines, path, seen1, pred, 500)
    assert status2 == :skipped
    assert Enum.count(Corpus.stream(path)) == 1
  end

  test "refresh_seed_pool! merges a banked closed typed_term into the live crossover pool" do
    # A real closed :typed_term seed from the tracked corpus is guaranteed to
    # round-trip through Corpus encode/decode and pass SeedPool.load's closed?
    # filter — the only challenge shape this feedback path picks up.
    ch =
      Corpus.stream("test/antigen/seeds.sexp")
      |> Enum.find_value(fn
        {:ok, %Challenge{kind: :typed_term, payload: %{ctx: [], term: t}} = c} ->
          if Cure.Core.Term.closed?(t), do: c, else: nil

        _ ->
          nil
      end)

    assert ch, "fixture needs a closed :typed_term seed in test/antigen/seeds.sexp"
    type = ch.payload.type

    path = Path.join(System.tmp_dir!(), "edgepool_#{System.unique_integer([:positive])}.sexp")
    on_exit(fn -> File.rm_rf!(path) end)

    # pool BEFORE the bank does not know this type
    Process.put(:antigen_seed_pool, %{})
    refute Map.has_key?(Process.get(:antigen_seed_pool), type)

    # budget 0 = no shrink, so the banked challenge's recorded type is preserved
    {_st, _min, _seen} =
      Cover.bank_interesting(ch, [{Cure.Core.Eval, 99}], path, MapSet.new(), fn _ -> true end, 0)

    Cover.refresh_seed_pool!(path)

    pool = Process.get(:antigen_seed_pool)
    # crossover can now draw this type mid-run
    assert Map.has_key?(pool, type)
    assert Antigen.Generators.SeedPool.pool_gen(pool, type) != :none
  end

  test "guided_loop terminates, grows the edge corpus, and tags jackpots with coverage_delta" do
    tmp = Path.join("tmp", "guided_#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    edge_path = Path.join(tmp, "edge.sexp")
    report_dir = Path.join(tmp, "reports")
    out = Path.join(tmp, "guided_kcov.md")

    opts = [
      gen: Mix.Tasks.Antigen.default_gen(),
      assay: Antigen.CoverGuidedTest.CoverThenViolate,
      count: 30,
      guided_round: 10,
      plateau: 2,
      edge_corpus: edge_path,
      corpus_path: Path.join(tmp, "corpus.sexp"),
      seeds_path: Path.join(tmp, "seeds.sexp"),
      report_dir: report_dir,
      out: out
    ]

    result = Cover.guided_loop(opts)

    # (a) terminated with a summary (plateau or budget)
    assert is_map(result)
    assert result.rounds >= 1

    # a coverage report is written to --out (same format as the one-shot mode),
    # so guided and unguided runs are directly comparable
    assert File.exists?(out)
    assert File.read!(out) =~ "Kernel Coverage"

    # (b) the edge corpus grew — the cold-start round hits new kernel lines
    assert File.exists?(edge_path)
    assert Enum.count(Corpus.stream(edge_path)) >= 1

    # (c) a single infection report per jackpot carries coverage_delta in its
    # health map (not a second report)
    reports = Path.wildcard(Path.join(report_dir, "failure-*.txt"))
    assert reports != []
    assert Enum.any?(reports, fn p -> File.read!(p) =~ "coverage_delta" end)

    # cover torn down node-wide
    assert :cover.modules() == []
  end

  test "guided_loop --precise attributes coverage per-challenge and still banks + terminates" do
    tmp = Path.join("tmp", "guided_p_#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    edge_path = Path.join(tmp, "edge.sexp")

    opts = [
      gen: Mix.Tasks.Antigen.default_gen(),
      assay: Antigen.CoverGuidedTest.CoverThenViolate,
      precise: true,
      count: 20,
      guided_round: 10,
      plateau: 2,
      edge_corpus: edge_path,
      corpus_path: Path.join(tmp, "corpus.sexp"),
      seeds_path: Path.join(tmp, "seeds.sexp"),
      report_dir: Path.join(tmp, "reports")
    ]

    result = Cover.guided_loop(opts)

    assert result.rounds >= 1
    assert File.exists?(edge_path)
    # precise mode banks per-input (not one-per-round), so with distinct new-line
    # sets it can bank more than one edge from the cold-start round
    assert Enum.count(Corpus.stream(edge_path)) >= 1
    assert :cover.modules() == []
  end
end
