defmodule Cure.Elab.BoolAlwaysResolvesTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive

  test "Bool as a type annotation resolves to the inductive family with no import" do
    src = "mod M\n  fn id(b: Bool) -> Bool = b\n"
    {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :bool) == :"Std.Bool#Bool"

    assert %{type: {:pi, _g, {:data, :"Std.Bool#Bool", [], []}, {:data, :"Std.Bool#Bool", [], []}}} =
             Cure.Core.Env.get_def(env, :id)
  end

  test "a program using only Nat still works unaffected" do
    src = "mod M\n  fn f(n: Nat) -> Nat = n\n"
    assert {:ok, _env} = Cure.Elab.Program.elaborate(src)
  end
end
