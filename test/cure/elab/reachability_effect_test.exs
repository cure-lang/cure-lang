defmodule Cure.Elab.ReachabilityEffectTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Emit, Program}

  # The sequel to `reachability_let_test.exs`, and the reason walker drift is a CLASS of
  # defect rather than an incident.
  #
  # That test exists because `Program.global_refs/1` had no `:let` clause and so fell to its
  # fail-open `defp global_refs(_leaf), do: []`, making any global referenced only inside a
  # `let` invisible to `Program.reachable_def_names/2`. The clause was added — for `:let`
  # only. The `Effect` formers, which arrived in the same era and also carry arbitrary
  # subterms, were never given one, so the identical bug survived one former over: a global
  # referenced only inside an `effect_bind` was still invisible.
  #
  # `reachable_def_names/2` is the documented way to co-emit a transitive closure
  # (`test/cure/stdlib/typeclass_migration_test.exs` does exactly this before
  # `Emit.compile_and_load(functions: ...)`). Dropping a reachable global there emits a
  # module that calls a function it never defines.

  @src """
  mod M
    @extern(:erlang, :display, 1)
    fn emit(x: Int) -> Effect(Int)

    fn helper(x: Int) -> Int = x + 1

    fn g(x: Int) -> Effect(Int) =
      let r = emit(x)
      emit(helper(x))
  """

  # The `let r = <an effect>` sequencing point lowers to `{:effect_bind, emit(x), λr. …}`, so
  # `helper` is referenced ONLY from inside an effect node — nowhere else in `g`'s body.

  test "a global referenced only inside an effect node is reachable" do
    {:ok, env} = Program.elaborate(@src)
    assert :"M#helper" in Program.reachable_def_names(env, [:g])
  end

  test "co-emitting that closure produces a module that actually defines the callee" do
    {:ok, env} = Program.elaborate(@src)
    functions = Program.reachable_def_names(env, [:g])

    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.EffectReachProbe", functions: functions)

    # The consequence, made concrete: `g` calls `helper`, so the emitted module must define
    # it. Before the fix the closure omitted `helper` and the module called a function that
    # was never emitted.
    assert function_exported?(m, :helper, 1)
    assert m.helper(1) == 2
  end
end
