defmodule Cure.Elab.Phase5U5StdlibPolymorphismTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Inductive, Kernel, Sort, UniverseLevel}
  alias Cure.Elab.Program

  describe "U5 §18 / §21.3 single polymorphic stdlib definitions at arbitrary levels" do
    test "Equivalent works at Int (level 0), Type (level 1), and Type37 (level 38) with one definition" do
      source = """
      mod U5.PolyEquivalent
        use Std.Equivalent

        fn eq_int(n: Int) -> Equivalent(Int, n, n) = reflexive(n)
        fn eq_type(a: Type) -> Equivalent(Type, a, a) = reflexive(a)
        fn eq_type37(a: Type37) -> Equivalent(Type37, a, a) = reflexive(a)
        fn sym_type(a: Type, b: Type, p: Equivalent(Type, a, b)) -> Equivalent(Type, b, a) = sym(p)
      end
      """

      assert {:ok, env} = Program.elaborate(source)

      for name <- [
            :"U5.PolyEquivalent#eq_int",
            :"U5.PolyEquivalent#eq_type",
            :"U5.PolyEquivalent#eq_type37",
            :"U5.PolyEquivalent#sym_type"
          ] do
        assert :ok = Kernel.check_def(env, name)
      end
    end

    test "List and Option work over Int (level 0), Type (level 1), and Type37 (level 38)" do
      source = """
      mod U5.PolyContainers
        use Std.List
        use Std.Option

        fn list_of_int(n: Int) -> List(Int) = Cons(n, Nil())
        fn list_of_type(a: Type) -> List(Type) = Cons(a, Nil())
        fn list_of_type37(a: Type37) -> List(Type37) = Cons(a, Nil())

        fn opt_of_int(n: Int) -> Option(Int) = Some(n)
        fn opt_of_type(a: Type) -> Option(Type) = Some(a)
        fn opt_of_type37(a: Type37) -> Option(Type37) = Some(a)
      end
      """

      assert {:ok, env} = Program.elaborate(source)

      for name <- [
            :"U5.PolyContainers#list_of_int",
            :"U5.PolyContainers#list_of_type",
            :"U5.PolyContainers#list_of_type37",
            :"U5.PolyContainers#opt_of_int",
            :"U5.PolyContainers#opt_of_type",
            :"U5.PolyContainers#opt_of_type37"
          ] do
        assert :ok = Kernel.check_def(env, name)
      end
    end

    test "Sigma works over ordinary values, types, and higher-universe families with max(la, lb) sort" do
      source = """
      mod U5.PolySigma
        use Std.Sigma

        fn pair_small(n: Int) -> Sigma(x: Int, Int) = %[n, n]
        fn pair_type_and_val(a: Type, x: a) -> Sigma(t: Type, t) = %[a, x]
        fn pair_type37_and_val(a: Type37, x: a) -> Sigma(t: Type37, t) = %[a, x]
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      sigma = Inductive.get_family(env, :Sigma)

      assert [
               {:la, {:level_type}},
               {:lb, {:level_type}},
               {:a, {:type, {:finite, %UniverseLevel{constant: 0, atoms: [{{:var, 1}, 0}]}}}},
               {:b,
                {:pi, :unrestricted, {:var, 0},
                 {:type, {:finite, %UniverseLevel{constant: 0, atoms: [{{:var, 2}, 0}]}}}}}
             ] = sigma.params

      assert sigma.sort == Sort.finite(UniverseLevel.max(UniverseLevel.atom({:var, 3}), UniverseLevel.atom({:var, 2})))

      for name <- [
            :"U5.PolySigma#pair_small",
            :"U5.PolySigma#pair_type_and_val",
            :"U5.PolySigma#pair_type37_and_val"
          ] do
        assert :ok = Kernel.check_def(env, name)
      end
    end
  end
end
