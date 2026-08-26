defmodule Cure.Core.InterfaceMethodIndexTest do
  use ExUnit.Case, async: false

  alias Cure.Core.Env
  alias Cure.Elab.Interface

  test "method lookup cost does not grow with unrelated interfaces" do
    small = environment_with_interfaces(1)
    large = environment_with_interfaces(64)

    small_reductions = lookup_reductions(small)
    large_reductions = lookup_reductions(large)

    assert large_reductions < small_reductions * 2,
           "expected indexed lookup; 1 interface used #{small_reductions} reductions, " <>
             "64 interfaces used #{large_reductions}"
  end

  defp environment_with_interfaces(count) do
    Enum.reduce(1..count, Env.empty(), fn index, env ->
      method = String.to_atom("method_#{index}")
      descriptor = %{methods: %{method => %{name: method}}}
      Env.put_interface(env, String.to_atom("Interface#{index}"), descriptor)
    end)
  end

  defp lookup_reductions(env) do
    {before_reductions, _} = :erlang.statistics(:reductions)

    for _ <- 1..10_000 do
      assert Interface.for_method(env, :missing) == nil
    end

    {after_reductions, _} = :erlang.statistics(:reductions)
    after_reductions - before_reductions
  end
end
