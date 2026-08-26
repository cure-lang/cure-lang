defmodule Antigen.CoverTest do
  # :cover is node-wide global
  use ExUnit.Case, async: false
  alias Antigen.Cover

  test "cover_compilable? is true for a debug_info module, and with_cover cleans up" do
    assert Cover.cover_compilable?(Antigen.CoverFixture)
    # not instrumented before
    assert :cover.modules() == []

    result =
      Cover.with_cover([Antigen.CoverFixture], fn ->
        Antigen.CoverFixture.classify(5)
        :ran
      end)

    assert result == :ran
    # cover fully stopped afterward — instrumented module list is empty again.
    # (Confirmed against OTP: :cover.stop/0 does NOT stop the cover_server
    # process or make :cover.modules/0 raise — it unloads instrumented modules,
    # and :cover.modules/0 keeps returning a plain list, [] once none remain.)
    assert :cover.modules() == []
  end

  test "cover_compilable? is false for a beam without debug_info" do
    # Build a module with NO debug_info at test runtime (mirrors `erlc` with no
    # `+debug_info`) — Mix's elixirc always embeds debug_info project-wide, so
    # this is the only way to exercise the false branch without a global
    # compiler-option change. Without this case, cover_compilable?/1 could
    # vacuously always return true and no test would catch it.
    # Compile to a REAL .beam on disk (not in-memory :binary) and load via
    # :code.load_abs/1, so :code.which/1 resolves a real path and
    # cover_compilable?/1 actually reaches :beam_lib.chunks on it — this is
    # what exposes the sentinel-value bug (an in-memory :code.load_binary/3
    # load makes :code.which/1 return the literal atom given as the 2nd arg,
    # e.g. `nofile`, so :beam_lib.chunks fails with :enoent and the guard
    # returns false for the wrong reason, without exercising the real branch).
    dir = System.tmp_dir!()
    src_path = Path.join(dir, "antigen_no_debug_fixture.erl")

    File.write!(src_path, """
    -module(antigen_no_debug_fixture).
    -export([f/0]).
    f() -> ok.
    """)

    {:ok, :antigen_no_debug_fixture} =
      :compile.file(String.to_charlist(src_path), [{:outdir, String.to_charlist(dir)}])

    beam_no_ext = dir |> Path.join("antigen_no_debug_fixture") |> String.to_charlist()
    {:module, :antigen_no_debug_fixture} = :code.load_abs(beam_no_ext)

    try do
      refute Cover.cover_compilable?(:antigen_no_debug_fixture)
    after
      :code.purge(:antigen_no_debug_fixture)
      :code.delete(:antigen_no_debug_fixture)
    end
  end

  test "line_coverage reports covered and cold lines, excluding the line-0 pseudo-entry" do
    cov =
      Cover.with_cover([Antigen.CoverFixture], fn ->
        # hits :pos only
        Antigen.CoverFixture.classify(5)
        Cover.line_coverage(Antigen.CoverFixture)
      end)

    assert cov.total > 0
    # :neg / :zero never executed
    assert cov.cold != []
    assert Enum.all?(cov.covered ++ cov.cold, &is_integer/1)
    assert length(cov.covered) + length(cov.cold) == cov.total
    # :cover.analyse(mod, :coverage, :line) emits a {{Mod, 0}, {0, 1}}
    # pseudo-entry that must be filtered (it maps to no real source line).
    refute 0 in cov.cold
    refute 0 in cov.covered
  end

  test "run_report produces a per-module kernel coverage map and writes a report" do
    tmp = Path.join("tmp", "antigen_cov_#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    out = Path.join(tmp, "kcov.md")

    opts = [
      gen: Mix.Tasks.Antigen.default_gen(),
      count: 30,
      corpus_path: Path.join(tmp, "corpus.sexp"),
      seeds_path: Path.join(tmp, "seeds.sexp"),
      report_dir: tmp,
      out: out
    ]

    {coverage, report} = Antigen.Cover.run_report(opts)

    # every kernel module in @cover_modules gets a coverage entry
    for m <- Antigen.Cover.cover_modules(), do: assert(Map.has_key?(coverage, m))
    # a real campaign exercises the normalizer
    assert coverage[Cure.Core.Normalise].total > 0
    assert length(coverage[Cure.Core.Normalise].covered) > 0
    assert File.exists?(out)
    assert report =~ "Kernel Coverage"
    # cover cleaned up after the report run
    assert :cover.modules() == []
    File.rm_rf!(tmp)
  end
end
