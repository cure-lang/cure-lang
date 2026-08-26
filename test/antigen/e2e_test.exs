defmodule Antigen.E2ETest do
  use ExUnit.Case, async: true
  alias Antigen.{Runner, Generators}

  @tmp "tmp/antigen_e2e_test"
  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  test "explore over the real totality generator runs clean post-fix, still exercising the mutual-group shape" do
    result =
      Runner.explore(
        gen: Generators.Totality.gen(),
        corpus_path: Path.join(@tmp, "corpus.sexp"),
        seeds_path: Path.join(@tmp, "seeds.sexp"),
        report_dir: @tmp,
        count: 50
      )

    # Hole fixed ⇒ the certifier soundly rejects the diverging pair ⇒ no infection.
    assert result.infections == 0
    refute File.exists?(Path.join(@tmp, "latest.txt"))
    # ...but the run still generated and covered the mutual-group shape (health gate)
    assert MapSet.member?(result.health.coverage, :has_mutual_group)
    assert result.health.discard_rate == 0.0
  end
end
