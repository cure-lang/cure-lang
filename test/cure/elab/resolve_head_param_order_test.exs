defmodule Cure.Elab.ResolveHeadParamOrderTest do
  @moduledoc """
  Regression: instance dispatch must LOCATE the head-bearing parameter, not guess it.

  `Resolve.head_param_index/2` looked for a parameter whose interface-signature type is
  the bare head variable (`x : a`). A higher-kinded interface never has one — its head
  appears applied (`container : f(a)`) — so the lookup returned `nil` and the code fell
  back to `|| 0`, assuming the head-bearing parameter is declared first.

  Nothing in the parser or `Cure.Elab.Interface` enforces that ordering. `resolve_hkt_test.exs`
  passed only because its `fmap(container: f(a), g: (a) -> b)` happens to declare the
  applied-head parameter first. Reordering the parameters made `method_call/5` elaborate
  and classify the WRONG argument, reporting `{:no_instance, :Tagged, :Int}` for a
  correctly registered instance.

  `head_param_index/2` now locates a bare occurrence, then an applied one, matching the
  two shapes `Interface.collect_head_uses/3` already classifies.

  NOT covered here: a lambda argument declared BEFORE the argument that fixes its domain
  (`fmap(fn(x) -> x + 10, xs)`) still fails with `{:unsolved_metavariables, :deferred_argument}`.
  That is a general elaborator limitation — an ordinary polymorphic `app2(g: (a) -> b,
  xs: List(a))` fails the same way with no interface in sight — so these tests keep the
  non-head parameter a plain value to isolate the dispatch question.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "a higher-kinded interface dispatches on the f(a)-typed parameter declared second" do
    src = """
    mod P
      interface Tagged(f)
        fn tag(n: Int, c: f(a)) -> Int
      implementation Tagged for List
        fn tag(n: Int, c: List(a)) -> Int = n
      fn use_it(xs: List(Int)) -> Int = tag(7, xs)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a higher-kinded interface still dispatches when the f(a)-typed parameter is first" do
    src = """
    mod P
      interface Tagged(f)
        fn tag(c: f(a), n: Int) -> Int
      implementation Tagged for List
        fn tag(c: List(a), n: Int) -> Int = n
      fn use_it(xs: List(Int)) -> Int = tag(xs, 7)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a first-order interface dispatches on the bare-head parameter declared second" do
    src = """
    mod P
      interface Shown(a)
        fn shown(n: Int, x: a) -> Int
      implementation Shown for Int
        fn shown(n: Int, x: Int) -> Int = n
      fn use_it(k: Int) -> Int = shown(7, k)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
