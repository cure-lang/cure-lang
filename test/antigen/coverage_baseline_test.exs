defmodule Antigen.CoverageBaselineTest do
  @moduledoc """
  The **coverage-floor regression gate** (runs on every `mix test`). Re-measures
  per-module kernel line-coverage by a PURE, non-generative replay of the committed
  corpora (`Antigen.CoverageBaseline.measure/0`) and fails if any module drops below
  its committed floor (`coverage_baseline.sexp`).

  No generators, no seeds, no sampling — the measurement is a deterministic replay,
  so a red gate is always a real regression, never a flaky draw. The ONLY sanctioned
  way to move the floor is `mix antigen cover --record-new-coverage-baseline`
  (re-distils `coverage.sexp` + rewrites the floor); everyday runs never regenerate
  it, so coverage cannot silently drift down.

  `async: false`: `:cover` is node-wide global (mirrors `Antigen.CoverTest`).
  """
  use ExUnit.Case, async: false
  alias Antigen.CoverageBaseline, as: CB

  @regen "mix antigen cover --record-new-coverage-baseline"

  test "the committed coverage corpus decodes and replays git-clean" do
    path = CB.coverage_path()
    assert File.exists?(path), "missing #{path} — generate it with `#{@regen}`"

    before = File.read!(path)
    _ = CB.measure()
    assert File.read!(path) == before, "replay must not mutate the committed coverage corpus"
  end

  test "no module's kernel line-coverage has dropped below its committed floor" do
    case CB.read_baseline() do
      {:error, :missing} ->
        flunk("missing #{CB.baseline_path()} — generate it with `#{@regen}`")

      {:ok, floor} ->
        measured = CB.measure()
        regressions = CB.regressions(measured, floor)

        assert regressions == [],
               """
               Kernel coverage dropped below the committed floor:
               #{Enum.map_join(regressions, "\n", fn {mod, fcov, cur} -> "  #{inspect(mod)}: floor #{fcov}, now #{inspect(cur)}" end)}

               Either a change stopped exercising code it used to (fix the regression),
               or newly-added code is genuinely unreachable defensive-guard code — in
               which case accept the new floor by re-recording:
                 #{@regen}
               """
    end
  end

  test "the floor never claims more coverage than a module actually has" do
    {:ok, floor} = CB.read_baseline()
    measured = CB.measure()

    for {mod, %{covered: fcov, total: ftot}} <- floor do
      assert fcov <= ftot, "#{inspect(mod)} floor #{fcov} exceeds its total #{ftot}"

      if cur = measured[mod] do
        assert ftot == cur.total,
               "#{inspect(mod)} total changed (floor #{ftot} vs now #{cur.total}) — re-record: #{@regen}"
      end
    end
  end
end
