defmodule Cure.Core.BuiltinsSeedTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  test "seed/1 registers validated bool and nat" do
    env = Builtins.seed(Env.empty())
    assert Inductive.builtin(env, :bool) == :"Std.Bool#Bool"
    assert Inductive.builtin(env, :nat) == :"Std.Nat#Nat"
    assert Inductive.family?(env, :"Std.Bool#Bool")
    assert Inductive.family?(env, :"Std.Nat#Nat")
  end

  test "seeded bool family has exactly False and True" do
    env = Builtins.seed(Env.empty())
    names = env |> Inductive.ctors_of(:"Std.Bool#Bool") |> Enum.map(& &1.name) |> Enum.sort()
    assert names == [:"Std.Bool#False", :"Std.Bool#True"]
  end

  test "seeded nat family has exactly Z and S/1" do
    env = Builtins.seed(Env.empty())
    ctors = env |> Inductive.ctors_of(:"Std.Nat#Nat") |> Enum.map(fn c -> {c.name, length(c.args)} end) |> Enum.sort()
    assert ctors == [{:"Std.Nat#S", 1}, {:"Std.Nat#Z", 0}]
  end

  test "Int constructor fields retain canonical Nat when Nat is excluded" do
    env = Builtins.seed(Env.empty(), MapSet.new([:Nat]))

    for constructor <- [:FromNat, :NegativeSuccessor] do
      assert %{args: [{:_a0, {:data, :"Std.Nat#Nat", [], []}}]} =
               Inductive.get_ctor(env, constructor)
    end
  end
end
