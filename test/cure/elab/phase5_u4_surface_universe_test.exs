defmodule Cure.Elab.Phase5U4SurfaceUniverseTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive, Kernel, Sort, Term, UniverseLevel}
  alias Cure.Elab.Program

  describe "U4 surface syntax and use-site level inference (§19.4)" do
    test "universe-polymorphic identity infers omitted level arguments at Int, Type, and Type37" do
      source = """
      mod U4.PolyId
        fn id({l: UniverseLevel}, {a: Type(l)}, x: a) -> a = x
        fn at_int(n: Int) -> Int = id(n)
        fn at_type(t: Type) -> Type = id(t)
        fn at_type37(t: Type37) -> Type37 = id(t)
      end
      """

      assert {:ok, env} = Program.elaborate(source)

      for name <- [:"U4.PolyId#id", :"U4.PolyId#at_int", :"U4.PolyId#at_type", :"U4.PolyId#at_type37"] do
        assert :ok = Kernel.check_def(env, name)
        %{type: type, body: body} = Env.get_def(env, name)
        assert Term.closed?(type)
        assert Term.closed?(body)
      end

      assert %{type: {:pi, :erased, {:level_type}, _}} = Env.get_def(env, :"U4.PolyId#id")
    end

    test "explicit universe_zero, universe_succ, and universe_max elaborate to canonical levels" do
      source = """
      mod U4.LevelOps
        fn lift_id({a: UniverseLevel}, {b: UniverseLevel}, {t: Type(universe_max(a, universe_succ(b)))}, x: t) -> t = x
        fn zero_type(t: Type(universe_zero)) -> Type(universe_zero) = t
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def(env, :"U4.LevelOps#lift_id")
      assert :ok = Kernel.check_def(env, :"U4.LevelOps#zero_type")
    end

    test "data family storing Type37 infers least family sort Type38 without a ceiling" do
      source = """
      mod U4.HighFamily
        type BigBox = MkBigBox(Type37)
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      family = Inductive.get_family(env, :"U4.HighFamily#BigBox")
      assert family.sort == Sort.finite_closed(38)
      assert :ok = Kernel.check_family(env, family)
    end

    test "universe-polymorphic data family infers least upper bound Type(l)" do
      source = """
      mod U4.PolyBox
        type Box(l: UniverseLevel, a: Type(l)) indices ()
          MkBox : a -> Box(l, a)
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      family = Inductive.get_family(env, :"U4.PolyBox#Box")
      assert :ok = Kernel.check_family(env, family)
      assert {:finite, %UniverseLevel{constant: 0, atoms: [{{:var, 1}, 0}]}} = family.sort
    end

    test "TypeLimit and TypeLimitN parse and elaborate as limit sorts" do
      source = """
      mod U4.Limits
        fn id_limit({a: TypeLimit}, x: a) -> a = x
        fn id_limit3({a: TypeLimit3}, x: a) -> a = x
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def(env, :"U4.Limits#id_limit")
      assert :ok = Kernel.check_def(env, :"U4.Limits#id_limit3")
      assert %{type: {:pi, :erased, {:type, {:omega, 0}}, _}} = Env.get_def(env, :"U4.Limits#id_limit")
      assert %{type: {:pi, :erased, {:type, {:omega, 3}}, _}} = Env.get_def(env, :"U4.Limits#id_limit3")
    end

    test "UniverseLevel binder is forced to grade zero and rejects explicit linear grade" do
      erased_source = """
      mod U4.LevelGrade
        fn accept(l: UniverseLevel, {a: Type(l)}, x: a) -> a = x
      end
      """

      assert {:ok, env} = Program.elaborate(erased_source)
      assert %{type: {:pi, :erased, {:level_type}, _}} = Env.get_def(env, :"U4.LevelGrade#accept")

      linear_source = """
      mod U4.LinearLevel
        fn reject(@linear l: UniverseLevel) -> Int = 0
      end
      """

      assert {:error, _} = Program.elaborate(linear_source)
    end

    test "Type(0) and Type-in-Type are rejected" do
      nat_as_level = """
      mod U4.BadNatLevel
        fn bad({a: Type(0)}, x: a) -> a = x
      end
      """

      assert {:error, _} = Program.elaborate(nat_as_level)

      type_in_type = """
      mod U4.TypeInType
        fn bad() -> Type = Type
      end
      """

      assert {:error, _} = Program.elaborate(type_in_type)
    end
  end
end
