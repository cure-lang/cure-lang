defmodule Cure.Compiler.ModulePipeline.InterfaceTraversalHotpathTest do
  @moduledoc """
  Published interfaces repeatedly scan Core definitions to close the set of
  bodies that must remain transparent.  Core's node taxonomy is closed and
  documented, so this scan should dispatch on each node directly and reserve
  structural descent for extension metadata or future nodes.
  """

  use ExUnit.Case, async: true

  test "interface transparency scan specializes Core nodes and retains fallback descent" do
    source = File.read!("lib/cure/compiler/module_pipeline/interface.ex")

    assert source =~ "defp mentioned_globals({:pi"
    assert source =~ "defp mentioned_globals({:case"
    assert source =~ "defp mentioned_globals({:effect_bind"
    assert source =~ "defp mentioned_globals(term, acc) when is_tuple(term)"
  end
end
