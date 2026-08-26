defmodule Cure.Elab.DerivingRefusalTest do
  @moduledoc """
  What `deriving` generates, and what it declines to generate.

  Three defects, one shared cause: `Deriving.generate/3` built a body without ever
  consulting the interface it was deriving, or checking the container it was handed.

    * the body hardcoded `var("x")`/`var("y")` as its two scrutinees while the
      generated *signature* took its parameter names from the interface's real
      declaration — so `fn eq(a1: a, a2: a)` derived a body over two free variables
      the signature never bound. `deriving Equatable` worked only for interfaces that
      happened to spell their parameters `x`/`y`, which is what every fixture did.
    * a container with no `variant: true` entries (a `rec`'s field list) derived an
      instance whose method was `match(x, [])` — zero arms, unsatisfiable.
    * a constructor field of the bound type parameter's own type derived a body whose
      `eq` call on that field needed an `Equatable(a)` dictionary that nothing injects.

  The first is fixed. The other two now refuse, with an error naming the type. On the
  third, refusing is the point: the real fix is dictionary passing under a type
  constructor, and `Resolve.dict_arguments/5` matches only a parameter typed by the
  bare head variable — a `where Equatable(a)` clause alone would resolve
  `Equatable(Lst)`, the in-progress instance itself. See the comment on
  `check_no_constrained_field/4`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  @equatable "  interface Equatable(a)\n    fn eq(x: a, y: a) -> Bool\n"

  describe "the derived body binds the interface's own parameter names" do
    test "derived Equatable elaborates when the interface's eq params aren't named x/y" do
      src = """
      mod DvOne
        interface Equatable(a)
          fn eq(a1: a, a2: a) -> Bool
        type Color = Red | Green | Blue deriving Equatable
        fn eqSame() -> Bool = eq(Green, Green)
        fn eqDiff() -> Bool = eq(Red, Blue)
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      functions = Enum.uniq([:eqSame, :eqDiff] ++ Program.impl_def_names(env))
      {:ok, m} = Emit.compile_and_load(env, module: :"Cure.DvOneColor", functions: functions)

      assert apply(m, :eqSame, []) == true
      assert apply(m, :eqDiff, []) == false
    end

    test "derived Ord elaborates when the interface's lt params aren't named x/y" do
      src = """
      mod DvOneOrd
        interface Ord(a)
          fn lt(this: a, that: a) -> Bool
        type Color = Red | Green | Blue deriving Ord
        fn ltTrue() -> Bool = lt(Red, Blue)
        fn ltFalse() -> Bool = lt(Blue, Red)
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      functions = Enum.uniq([:ltTrue, :ltFalse] ++ Program.impl_def_names(env))
      {:ok, m} = Emit.compile_and_load(env, module: :"Cure.DvOneOrdColor", functions: functions)

      assert apply(m, :ltTrue, []) == true
      assert apply(m, :ltFalse, []) == false
    end
  end

  describe "refusals" do
    test "record fields derive as the record's single constructor" do
      {:ok, env} = Program.elaborate("mod DvThree\n" <> @equatable <> "end\n")

      fields = [
        {:param, [type: {:variable, [], "Int"}], "x"},
        {:param, [type: {:variable, [], "Int"}], "y"}
      ]

      container = {:container, [container_type: :struct, name: "Point", type_params: []], fields}

      assert {:ok, {:implementation, [{:interface, "Equatable"} | _], [_method]}} =
               Cure.Elab.Deriving.generate(:Equatable, container, env)
    end

    test "a constructor field of the bound type parameter's type is refused" do
      src =
        "mod DvTwo\n" <> @equatable <> "  type Lst(a) = Nil | Cons(a, Lst(a)) deriving Equatable\nend\n"

      assert {:error, error} = Program.elaborate(src)
      assert {:deriving_needs_constraints, :Equatable, :Lst} = Program.semantic_error(error)
    end

    test "a parameterized type with no field of the parameter's type still derives" do
      src = "mod DvBox\n" <> @equatable <> "  type Box(a) = Empty | Full deriving Equatable\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "a field of the recursive family itself still derives — it resolves to this instance" do
      src =
        "mod DvTree\n" <>
          @equatable <> "  type Tree(a) = Leaf | Node(Tree(a), Tree(a)) deriving Equatable\nend\n"

      assert {:ok, _env} = Program.elaborate(src)
    end
  end
end
