defmodule Cure.Compiler.Parser.FixityScanHotpathTest do
  @moduledoc """
  Fixity harvesting scans every syntax node once per expansion round.  The
  tuple shape is dynamic, but its children can be visited by index without
  allocating a temporary list for every AST node.
  """

  use ExUnit.Case, async: true

  test "structural scanners use indexed tuple traversal helpers" do
    source = File.read!("lib/cure/compiler/parser/fixity_scan.ex")

    assert source =~ "defp deep_collect_tuple"
    assert source =~ "defp deep_scan_tuple"
    assert source =~ "defp deep_reduce_tuple"
    assert source =~ "defp collect_qualified_targets_tuple"
  end
end
