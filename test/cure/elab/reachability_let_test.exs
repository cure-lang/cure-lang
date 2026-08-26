defmodule Cure.Elab.ReachabilityLetTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Emit, Program}

  # `Program.global_refs/1` enumerates the Core formers it knows and ends in a
  # fail-open `defp global_refs(_leaf), do: []`. When the `:let` binder landed as
  # the seventh Core former, no clause was added for it — so every global
  # referenced only inside a `let` became invisible to
  # `Program.reachable_def_names/2`.
  #
  # That function is the documented way to co-emit a transitive closure
  # (`test/cure/stdlib/typeclass_migration_test.exs` does exactly this before
  # `Emit.compile_and_load(functions: ...)`). Dropping a reachable global there
  # emits a module that calls a function it never defined.

  test "a global referenced only inside a let is reachable" do
    src = """
    mod M
      fn helper(x: Int) -> Int = x + 1

      fn g(x: Int) -> Int =
        let y: Int = helper(x)
        y + y
    """

    {:ok, env} = Program.elaborate(src)
    assert :"M#helper" in Program.reachable_def_names(env, [:g])
  end

  test "co-emitting that closure produces a module that actually runs" do
    src = """
    mod M
      fn helper(x: Int) -> Int = x + 1

      fn g(x: Int) -> Int =
        let y: Int = helper(x)
        y + y
    """

    {:ok, env} = Program.elaborate(src)
    functions = Program.reachable_def_names(env, [:g])

    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.LetReachProbe", functions: functions)

    # helper(1) = 2, then y + y = 4.
    assert apply(m, :g, [1]) == 4
  end

  test "globals in a let's type and value positions are both found" do
    # The `:let` former is {:let, type, value, body}; all three are terms.
    src = """
    mod M
      fn a(x: Int) -> Int = x
      fn b(x: Int) -> Int = x

      fn g(x: Int) -> Int =
        let y: Int = a(x)
        b(y)
    """

    {:ok, env} = Program.elaborate(src)
    reachable = Program.reachable_def_names(env, [:g])
    assert :"M#a" in reachable
    assert :"M#b" in reachable
  end
end
