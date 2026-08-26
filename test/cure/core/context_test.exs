defmodule Cure.Core.ContextTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Context

  test "empty context has length 0 and an empty env" do
    assert Context.length(Context.empty()) == 0
    assert Context.env(Context.empty()) == []
  end

  test "extend then lookup returns the most-recent type at index 0" do
    ctx = Context.empty() |> Context.extend({:vtype, 0}) |> Context.extend({:vtype, 1})
    assert Context.length(ctx) == 2
    assert Context.lookup(ctx, 0) == {:vtype, 1}
    assert Context.lookup(ctx, 1) == {:vtype, 0}
  end

  test "env yields fresh neutrals; index 0 (most recent) is the highest level" do
    ctx = Context.empty() |> Context.extend({:vtype, 0}) |> Context.extend({:vtype, 1})
    assert Context.env(ctx) == [{:vneutral, {:nvar, 1}}, {:vneutral, {:nvar, 0}}]
  end
end
