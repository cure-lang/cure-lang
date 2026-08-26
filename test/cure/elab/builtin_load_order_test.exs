defmodule Cure.Elab.BuiltinLoadOrderTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive

  # Task 4.5 seeds Bool/Nat into env0 before any declaration of the compiled
  # module is processed, so there is no "first declaration in some group" race to
  # guard. If either of these fails, Task 4.5's env0 seeding is incomplete — do
  # not add an ordering fix here.
  test ":bool is seeded even when a Bool-typed comparison is the module's very first declaration" do
    src = "mod M\n  fn use_eq(a: Int, b: Int) -> Bool = a == b\n"
    assert {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :bool) == :"Std.Bool#Bool"
  end

  test ":nat is seeded even when Nat is the module's very first declaration" do
    src = "mod M\n  fn first(n: Nat) -> Nat = n\n"
    assert {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert Inductive.builtin(env, :nat) == :"Std.Nat#Nat"
  end
end
