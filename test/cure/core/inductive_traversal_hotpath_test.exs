defmodule Cure.Core.InductiveTraversalHotpathTest do
  @moduledoc """
  The positivity kernel walks Core terms very frequently while interfaces are
  built.  These terms have a closed, documented shape, so the hot path must
  dispatch on that shape directly instead of converting every node to a list.

  The final catch-all remains mandatory: malformed or future Core nodes must be
  traversed fail-closed rather than silently treated as absent.  This test is a
  source-level guard for the optimization boundary; the positivity behavior is
  covered by the soundness regressions alongside it.
  """

  use ExUnit.Case, async: true

  test "positivity walkers specialize the Core node shapes and retain a fallback" do
    source = File.read!("lib/cure/core/inductive.ex")

    assert source =~ "defp occurs?(env, fname, {:pi"
    assert source =~ "defp occurs?(env, fname, {:case"
    assert source =~ "defp gather_data_heads({:pi"
    assert source =~ "defp gather_data_heads({:case"

    # Unknown/future nodes still take the fail-closed structural fallback.
    assert source =~ "defp occurs?(env, fname, t, seen) when is_tuple(t)"
    assert source =~ "defp gather_data_heads(t, env, acc, seen) when is_tuple(t)"
  end
end
