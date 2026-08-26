defmodule Antigen.CoverReportTest do
  use ExUnit.Case, async: false
  alias Antigen.{Cover, CoverReport}

  test "function_index maps lines to {fun, arity}, keyed by plain integer lines" do
    idx = CoverReport.function_index(Antigen.CoverFixture)
    assert Enum.any?(idx, fn {_line, fa} -> fa == {:classify, 1} end)
    # This is the assertion that actually catches a missing :erl_anno.line/1
    # normalization: if a key were left as the raw {Line, Column} anno tuple,
    # `Enum.any?` above would still find the {:classify, 1} value (only the
    # VALUE is checked there) — the key-shape check below is what fails.
    assert Enum.all?(idx, fn {line, _fa} -> is_integer(line) end)
    # Cross-check against line_coverage/1's own (confirmed integer) keys —
    # function_index must be usable to look up cover's real cold lines.
    cold_lines =
      Cover.with_cover([Antigen.CoverFixture], fn ->
        Antigen.CoverFixture.classify(5)
        Cover.line_coverage(Antigen.CoverFixture)
      end).cold

    assert Enum.all?(cold_lines, &Map.has_key?(idx, &1))
  end

  test "render is deterministic and groups cold lines by function" do
    covmap = %{Antigen.CoverFixture => %{covered: [5], cold: [3, 4], total: 3}}
    idx = CoverReport.function_index(Antigen.CoverFixture)
    out1 = CoverReport.render(covmap, %{Antigen.CoverFixture => idx})
    out2 = CoverReport.render(covmap, %{Antigen.CoverFixture => idx})
    assert out1 == out2
    assert out1 =~ "classify/1"
  end
end
