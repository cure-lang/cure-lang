defmodule Cure.Stdlib.ShrinkInterfaceTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # `Std.Gen.shrink` was postulated as
  #
  #     @extern(:cure_std_gen, :shrink, 1)
  #     fn shrink(v: t) -> List(t)
  #
  # i.e. `∀t. t -> List(t)`. The implementation dispatches on the runtime
  # representation (`is_integer`, `is_list`, `is_tuple`, then `[]`). No
  # parametric inhabitant of that type can do that: the free theorem requires
  # `shrink(g x) == map(g, shrink x)` for every `g`, and it does not hold —
  #
  #     shrink(g 4)      = []                         (g : Int -> String)
  #     map(g, shrink 4) = ["", "aa", "a", "aaa"]
  #
  # Cure erases type arguments, so any future optimisation appealing to
  # parametricity is unsound while that axiom stands.
  #
  # A typeclass method, by contrast, is *permitted* to dispatch on `t` — the
  # dictionary is a real argument. So `shrink` becomes `interface Shrink(t)`.

  @gen_source File.read!("lib/std/gen.cure")

  test "Std.Gen no longer postulates a polymorphic shrink" do
    refute @gen_source =~ "@extern(:cure_std_gen, :shrink, 1)",
           "the parametricity-violating axiom is still declared"

    assert @gen_source =~ "interface Shrink(t)"
  end

  test "Std.Gen keeps its two honest monomorphic shrinker axioms" do
    assert @gen_source =~ "@extern(:cure_std_gen, :shrink_int, 1)"
    assert @gen_source =~ "@extern(:cure_std_gen, :shrink_list, 1)"
  end

  test "a Shrink method resolves to the Int instance" do
    src = """
    mod M
      interface Shrink(t)
        fn shrink(v: t) -> List(t)

      implementation Shrink for Int
        fn shrink(v: Int) -> List(Int) = [v]

      fn f(x: Int) -> List(Int) = shrink(x)
    """

    assert {:ok, env} = Program.elaborate(src)
    assert :"M#__impl_Shrink_Std.Int#Int_shrink" in Program.impl_def_names(env)
    assert inspect(Map.get(env.defs, :"M#f").body) =~ "__impl_Shrink_Std.Int#Int_shrink"
  end

  test "shrink at a type with no instance is rejected — what ∀t. t -> List(t) could never do" do
    src = """
    mod N
      interface Shrink(t)
        fn shrink(v: t) -> List(t)

      implementation Shrink for Int
        fn shrink(v: Int) -> List(Int) = [v]

      fn g(a: Atom) -> List(Atom) = shrink(a)
    """

    assert {:error,
            {:source_context, {:no_instance, :Shrink, :Atom},
             %{
               expectation_origin: :implicit,
               expression_category: :function_call,
               checking: "shrink",
               line: 8,
               column: 33
             }}} = Program.elaborate(src)
  end

  test "the Elixir shrink/1 survives as an internal helper, not an axiom" do
    # `cure_std_test.ex`'s shrink_loop calls it dynamically. It is no longer
    # pointed at by any @extern, so it is not part of the axiom surface.
    assert :cure_std_gen.shrink(4) != []
    assert is_list(:cure_std_gen.shrink([1, 2, 3]))
    assert :cure_std_gen.shrink(:an_atom) == []
  end
end
