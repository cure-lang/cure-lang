defmodule Cure.Core.ContextTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Context

  test "empty context has length 0 and an empty env" do
    assert Context.length(Context.empty()) == 0
    assert Context.env(Context.empty()) == []
  end

  test "extend then lookup returns the most-recent type at index 0" do
    ctx =
      Context.empty()
      |> Context.extend({:vtype, {:finite, %Cure.Core.LevelValue{constant: 0, atoms: []}}})
      |> Context.extend({:vtype, {:finite, %Cure.Core.LevelValue{constant: 1, atoms: []}}})

    assert Context.length(ctx) == 2
    assert Context.lookup(ctx, 0) == {:vtype, {:finite, %Cure.Core.LevelValue{constant: 1, atoms: []}}}
    assert Context.lookup(ctx, 1) == {:vtype, {:finite, %Cure.Core.LevelValue{constant: 0, atoms: []}}}
  end

  test "env yields fresh neutrals; index 0 (most recent) is the highest level" do
    ctx =
      Context.empty()
      |> Context.extend({:vtype, {:finite, %Cure.Core.LevelValue{constant: 0, atoms: []}}})
      |> Context.extend({:vtype, {:finite, %Cure.Core.LevelValue{constant: 1, atoms: []}}})

    assert Context.env(ctx) == [{:vneutral, {:nvar, 1}}, {:vneutral, {:nvar, 0}}]
  end
end
