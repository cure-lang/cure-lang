defmodule Cure.Elab.ResolveHktTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "fmap over List resolves via type-constructor extraction and runs; element type changes" do
    # `map` is defined locally rather than pulled from `Std.List`: the interface
    # resolution under test only needs `List` (a builtin family) and a mapping
    # function. `use Std.List` additionally elaborates unrelated helpers
    # (`uncons`/`split_first`) that depend on the still-open flat-tuple value
    # surface (#23), which would mask this test's subject.
    src = """
    mod H1
      fn lmap(xs: List(a), g: a -> b) -> List(b) =
        match xs
          [] -> []
          [h | t] -> [g(h) | lmap(t, g)]
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
      implementation Functor for List
        fn fmap(container: List(a), g: a -> b) -> List(b) = lmap(container, g)
      fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 10)
    end
    """

    {:ok, env} = Program.elaborate(src)
    functions = Enum.uniq([:bump, :lmap | Program.impl_def_names(env)])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.H1", functions: functions)
    assert apply(m, :bump, [[1, 2, 3]]) == [11, 12, 13]
  end

  test "a Functor method on a non-applied type is a clean no_instance error" do
    src = """
    mod H2
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
      fn bad(x: Int) -> Int = fmap(x, fn(y) -> y)
    end
    """

    assert {:error, {:source_context, {:no_instance, :Functor, _}, _}} = Program.elaborate(src)
  end
end
