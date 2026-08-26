defmodule Mix.Tasks.AntigenTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  @tmp "tmp/antigen_task_test"
  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "cover_dispatch routes --guided to :guided and threads precise/edge_corpus/out" do
    runner_opts = [gen: :g, count: 10, corpus_path: "c.sexp"]

    {mode, merged} =
      Mix.Tasks.Antigen.cover_dispatch(
        [guided: true, precise: true, edge_corpus: "e.sexp", out: "o.md"],
        runner_opts
      )

    assert mode == :guided
    assert merged[:precise] == true
    assert merged[:edge_corpus] == "e.sexp"
    assert merged[:out] == "o.md"
    # runner_opts preserved
    assert merged[:corpus_path] == "c.sexp"

    {mode2, merged2} = Mix.Tasks.Antigen.cover_dispatch([], runner_opts)
    assert mode2 == :report
    assert merged2[:precise] == false
    assert merged2[:edge_corpus] == nil
    # loop-tuning flags are only threaded when present, so guided_loop's own
    # defaults apply otherwise (Keyword.get default would break on an explicit nil)
    refute Keyword.has_key?(merged2, :plateau)
    refute Keyword.has_key?(merged2, :guided_round)

    {_m3, merged3} = Mix.Tasks.Antigen.cover_dispatch([guided: true, plateau: 9, guided_round: 25], runner_opts)
    assert merged3[:plateau] == 9
    assert merged3[:guided_round] == 25
  end

  test "mix antigen --count runs the explorer and prints a summary" do
    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.run([
          "--count",
          "50",
          "--corpus",
          Path.join(@tmp, "corpus.sexp"),
          "--seeds",
          Path.join(@tmp, "seeds.sexp"),
          "--report-dir",
          @tmp
        ])
      end)

    assert out =~ "antigen" and (out =~ "infection" or out =~ "banked")
  end

  test "mix antigen generate --count harvests seeds and writes no infection reports" do
    Mix.Tasks.Antigen.run([
      "generate",
      "--count",
      "50",
      "--seeds",
      Path.join(@tmp, "seeds.sexp"),
      "--report-dir",
      @tmp
    ])

    assert File.exists?(Path.join(@tmp, "seeds.sexp"))
    refute File.exists?(Path.join(@tmp, "latest.txt"))
  end

  test "mix antigen complete checks coverage and replay without banking" do
    corpus = Path.join(@tmp, "empty-corpus.sexp")

    out =
      capture_io(fn ->
        Mix.Tasks.Antigen.run(["complete", "--corpus", corpus])
      end)

    assert out =~ "Antigen completion: 318/318"
    refute File.exists?(Path.join(@tmp, "seeds.sexp"))
  end

  test "the wired-in default_gen draws :typed_term challenges (Tier B is live)" do
    seeds_path = Path.join(@tmp, "seeds_tier_b.sexp")

    Mix.Tasks.Antigen.run([
      "generate",
      "--count",
      "300",
      "--seeds",
      seeds_path,
      "--report-dir",
      @tmp
    ])

    kinds =
      Antigen.Corpus.stream(seeds_path)
      |> Enum.flat_map(fn
        {:ok, c} -> [c.kind]
        _ -> []
      end)
      |> MapSet.new()

    assert :typed_term in kinds
  end

  test "the wired-in default_gen draws :mutant_term challenges" do
    seeds_path = Path.join(@tmp, "seeds_mutant.sexp")

    Mix.Tasks.Antigen.run([
      "generate",
      "--count",
      "300",
      "--seeds",
      seeds_path,
      "--report-dir",
      @tmp
    ])

    kinds =
      Antigen.Corpus.stream(seeds_path)
      |> Enum.flat_map(fn
        {:ok, c} -> [c.kind]
        _ -> []
      end)
      |> MapSet.new()

    assert :mutant_term in kinds
  end

  test "budget_to_count converts minutes to a round count via the fixed rounds-per-minute constant" do
    one_minute = Mix.Tasks.Antigen.budget_to_count("1m")
    assert one_minute > 0
    assert Mix.Tasks.Antigen.budget_to_count("2m") == one_minute * 2
  end
end
