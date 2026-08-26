defmodule Cure.Stdlib.TypeclassMigrationTest do
  # The 5 stdlib protocol modules migrated from runtime `proto`/`impl` to
  # compile-time `interface`/`implementation`. Each must elaborate on the
  # DEPENDENT pipeline and its methods resolve + run. Grown one module at a time.
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  describe "Std.Functor (higher-kinded)" do
    test "the module elaborates as an interface on the dependent pipeline" do
      assert {:ok, _env} = Program.elaborate(File.read!("lib/std/functor.cure"))
    end

    test "fmap over a List resolves via the imported List instance (HKT)" do
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """

      # HKT resolution recovers the `List` head constructor from `f(a) = List(Int)`
      # and selects the imported instance's method — proving `interface`/`instance`
      # state crosses the `use` boundary (merge_env unions interfaces + coherence).
      assert {:ok, env} = Program.elaborate(src)
      refute :"Std.Functor#__impl_Functor_Std.List#List_fmap" in Program.impl_def_names(env)

      assert inspect(Map.get(env.defs, :"M#bump").body) =~
               "__impl_Functor_Std.List#List_fmap"
    end

    test "the imported instance remains owned and emitted by Std.Functor" do
      # An importer needs the instance signature and coherence entry, not its
      # ordinary runtime body. The canonical interface keeps that body opaque;
      # calls retain the qualified instance identity and route to the single
      # implementation emitted by Std.Functor.
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """

      {:ok, env} = Program.elaborate(src)
      impl = Map.get(env.defs, :"Std.Functor#__impl_Functor_Std.List#List_fmap")
      assert impl.body == {:hole, "__interface_opaque__"}

      assert inspect(Map.get(env.defs, :"M#bump").body) =~
               "Std.Functor#__impl_Functor_Std.List#List_fmap"
    end

    test "fmap over a List runs end-to-end (#23 cross-module polymorphic calls)" do
      src = """
      mod M
        use Std.List
        use Std.Functor
        fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
      """

      {:ok, env} = Program.elaborate(src)
      # Only M's body is emitted here; the qualified instance call stays remote.
      roots = [:bump | Program.impl_def_names(env)]
      functions = Program.reachable_def_names(env, roots)
      {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: functions)
      assert apply(m, :bump, [[1, 2, 3]]) == [11, 12, 13]
    end
  end
end
