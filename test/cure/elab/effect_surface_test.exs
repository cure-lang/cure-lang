defmodule Cure.Elab.EffectSurfaceTest do
  # Surface `Effect(T)` in a TYPE position lowers to the kernel's inert effect
  # type former `{:effect_type, ⟦T⟧}` (design 2026-07-09-effect-type-former §3).
  # The kernel already types that node; this exercises the surface→Core wiring:
  #   * a function return type `-> Effect(Unit)` lowers to `{:effect_type, …}`,
  #   * an effectful `@extern` postulate registers with that return type,
  #   * a single-effect-call body kernel-checks green,
  #   * the argument is lowered RECURSIVELY (so `Effect(List(Int))` works),
  #   * `Effect` over a non-type is rejected by the kernel.
  # NOTE: effectful `let`-sequencing / `pure` / `bind` surface syntax is a LATER
  # slice and is deliberately NOT exercised here. (`yield` is a reserved keyword,
  # so the effectful extern is spelled `sched_yield`, still targeting erlang:yield/0.)
  use ExUnit.Case, async: true

  alias Cure.Elab.{Declarations, Program}
  alias Cure.Core.{Context, Env, Kernel}

  defp type_of(env, name), do: Env.get_def(env, name).type

  # A prelude-bearing env (List + Int registered) obtained by elaborating a
  # trivial module, so `lower_type` can resolve `List`/`Int` in argument position.
  defp prelude_env do
    src = """
    mod Base
      use Std.List
      fn seed(x: List(Int)) -> List(Int) = x
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    env
  end

  describe "surface Effect(T) in a return-type position" do
    test "fn f() -> Effect(Unit) lowers its return type to {:effect_type, Unit}" do
      src = """
      mod M
        @extern(:erlang, :yield, 0)
        fn sched_yield() -> Effect(Unit)
        fn f() -> Effect(Unit) = sched_yield()
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:effect_type, {:data, :"Std.Unit#Unit", [], []}} = type_of(env, :f)
    end

    test "an effectful @extern registers a postulate whose type ends in {:effect_type, …}" do
      src = """
      mod M
        @extern(:erlang, :yield, 0)
        fn sched_yield() -> Effect(Unit)
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:effect_type, {:data, :"Std.Unit#Unit", [], []}} = type_of(env, :sched_yield)
      assert {:extern, {:erlang, :yield, 0}} = Env.get_def(env, :sched_yield).body
    end

    test "a single-effect-call body kernel-checks green (Effect(Int))" do
      src = """
      mod M
        @extern(:erlang, :make_ref, 0)
        fn mkref() -> Effect(Int)
        fn f() -> Effect(Int) = mkref()
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:effect_type, {:data, :"Std.Int#Int", [], []}} = type_of(env, :f)
    end
  end

  describe "recursive argument lowering" do
    test "Effect(Int) lowers to {:effect_type, Std.Int#Int}" do
      ast = {:function_call, [name: "Effect"], [{:variable, [scope: :local], "Int"}]}
      assert {:ok, {:effect_type, {:data, :"Std.Int#Int", [], []}}} = Declarations.lower_type(ast, [], prelude_env())
    end

    test "Effect(List(Int)) lowers its argument through idx_to_core recursively" do
      inner = {:function_call, [name: "List"], [{:variable, [scope: :local], "Int"}]}
      ast = {:function_call, [name: "Effect"], [inner]}

      assert {:ok, {:effect_type, {:data, :"Std.List#List", [{:data, :"Std.Int#Int", [], []}], []}}} =
               Declarations.lower_type(ast, [], prelude_env())
    end
  end

  describe "kind discipline" do
    test "Effect over a non-type (a Nat literal) is rejected by the kernel" do
      env = prelude_env()
      ast = {:function_call, [name: "Effect"], [{:variable, [scope: :local], "3"}]}

      assert {:ok, {:effect_type, {:nat_lit, 3}}} = Declarations.lower_type(ast, [], env)
      assert {:error, _} = Kernel.infer(Context.empty(env), {:effect_type, {:nat_lit, 3}})
    end
  end
end
