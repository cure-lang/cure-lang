defmodule Cure.Elab.DerivingTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # A module carrying the `Equatable`/`Ord` interfaces, their primitive `Int`
  # instances, and a recursive `Tree` that derives both. `extra` appends the
  # per-test probe functions. The interface methods (`eq`/`lt`) are invoked
  # DIRECTLY — never `==`/`<` — so the call routes through instance resolution
  # (Task 4) and goes red with `{:no_instance, …}` until deriving generates the
  # `Tree` instance. A `==`-phrased test would evaluate on BEAM's native `==`
  # with no instance at all and never go red.
  defp tree_src(extra) do
    """
    mod DT
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
      interface Ord(a)
        fn lt(x: a, y: a) -> Bool
      implementation Equatable for Int
        fn eq(x: Int, y: Int) -> Bool = x == y
      implementation Ord for Int
        fn lt(x: Int, y: Int) -> Bool = x < y
      type Tree = Leaf | Node(Tree, Int, Tree) deriving Equatable, Ord
    #{extra}
    end
    """
  end

  defp load(src, probes) do
    {:ok, env} = Program.elaborate(src)
    functions = Enum.uniq(probes ++ Program.impl_def_names(env))
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.DT", functions: functions)
    m
  end

  # The interfaces + primitive `Int` instances, with `tail` (a type declaration
  # plus probe functions) appended. Lets the edge-case tests derive over a
  # single-constructor type / an all-nullary enum without the `Tree` shape.
  defp derive_src(tail) do
    """
    mod DT
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
      interface Ord(a)
        fn lt(x: a, y: a) -> Bool
      implementation Equatable for Int
        fn eq(x: Int, y: Int) -> Bool = x == y
      implementation Ord for Int
        fn lt(x: Int, y: Int) -> Bool = x < y
    #{tail}
    end
    """
  end

  test "derived Equatable on a recursive ADT: equal → true, unequal → false" do
    src =
      tree_src("""
        fn t1() -> Tree = Node(Leaf, 1, Node(Leaf, 2, Leaf))
        fn t2() -> Tree = Node(Leaf, 1, Node(Leaf, 2, Leaf))
        fn t3() -> Tree = Node(Leaf, 1, Node(Leaf, 9, Leaf))
        fn eqSame() -> Bool = eq(t1(), t2())
        fn eqDiff() -> Bool = eq(t1(), t3())
      """)

    m = load(src, [:eqSame, :eqDiff, :t1, :t2, :t3])
    assert apply(m, :eqSame, []) == true
    assert apply(m, :eqDiff, []) == false
  end

  test "derived Ord: orders by constructor then field, lexicographically" do
    src =
      tree_src("""
        fn ctorOrder() -> Bool = lt(Leaf, Node(Leaf, 1, Leaf))
        fn ctorOrderRev() -> Bool = lt(Node(Leaf, 1, Leaf), Leaf)
        fn fieldLt() -> Bool = lt(Node(Leaf, 1, Leaf), Node(Leaf, 2, Leaf))
        fn fieldGt() -> Bool = lt(Node(Leaf, 2, Leaf), Node(Leaf, 1, Leaf))
      """)

    m = load(src, [:ctorOrder, :ctorOrderRev, :fieldLt, :fieldGt])
    assert apply(m, :ctorOrder, []) == true
    assert apply(m, :ctorOrderRev, []) == false
    assert apply(m, :fieldLt, []) == true
    assert apply(m, :fieldGt, []) == false
  end

  # A single-constructor type exercises the `single`-ctor branch: the inner
  # `match` needs no wildcard `_ -> false` arm (one constructor is exhaustive),
  # and `Ord`'s inner `match` has no cross-constructor arms.
  test "derived Equatable/Ord on a single-constructor type" do
    src =
      derive_src("""
        type Box = MkBox(Int) deriving Equatable, Ord
        fn eqSame() -> Bool = eq(MkBox(3), MkBox(3))
        fn eqDiff() -> Bool = eq(MkBox(3), MkBox(4))
        fn ltTrue() -> Bool = lt(MkBox(3), MkBox(4))
        fn ltFalse() -> Bool = lt(MkBox(4), MkBox(3))
      """)

    m = load(src, [:eqSame, :eqDiff, :ltTrue, :ltFalse])
    assert apply(m, :eqSame, []) == true
    assert apply(m, :eqDiff, []) == false
    assert apply(m, :ltTrue, []) == true
    assert apply(m, :ltFalse, []) == false
  end

  # An all-nullary enum exercises the empty-field folds (`eq` conjunction of no
  # pairs is `true`; `lt`'s lexicographic fold of no fields is `false`) and pure
  # constructor-order ranking (`Red < Green < Blue`).
  test "derived Equatable/Ord on an all-nullary enum: constructor-order ranking" do
    src =
      derive_src("""
        type Color = Red | Green | Blue deriving Equatable, Ord
        fn eqSame() -> Bool = eq(Green, Green)
        fn eqDiff() -> Bool = eq(Red, Blue)
        fn ltTrue() -> Bool = lt(Red, Blue)
        fn ltFalse() -> Bool = lt(Blue, Red)
        fn ltEqual() -> Bool = lt(Green, Green)
      """)

    m = load(src, [:eqSame, :eqDiff, :ltTrue, :ltFalse, :ltEqual])
    assert apply(m, :eqSame, []) == true
    assert apply(m, :eqDiff, []) == false
    assert apply(m, :ltTrue, []) == true
    assert apply(m, :ltFalse, []) == false
    assert apply(m, :ltEqual, []) == false
  end

  test "deriving Show publishes a record implementation" do
    {:ok, env} =
      Program.elaborate("""
      mod E
        type String = Text
        interface Show(a)
          fn show(value: a) -> String
      end
      """)

    record = {:container, [container_type: :struct, name: "Color"], []}

    assert {:ok, {:implementation, [{:interface, "Show"} | _], [_method]}} =
             Cure.Elab.Deriving.generate(:Show, record, env)
  end
end
