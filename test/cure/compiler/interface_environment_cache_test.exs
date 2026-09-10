defmodule Cure.Compiler.ModulePipeline.InterfaceEnvironmentCacheTest do
  @moduledoc """
  `Interface.to_env/1` is called at every edge while a dependency closure is
  assembled.  The conversion is pure and keyed by the interface's semantic
  hash, so repeated conversions in one compiler process should reuse it.
  """

  use ExUnit.Case, async: true

  test "to_env has an explicit process-local semantic-interface cache" do
    source = File.read!("lib/cure/compiler/module_pipeline/interface.ex")

    assert source =~ "@to_env_cache_key"
    assert source =~ "defp to_env_uncached"
    assert source =~ "Process.get(@to_env_cache_key"
  end
end
